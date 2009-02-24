#!/usr/bin/env python2.5

'''
Synchronize the contents of a Google AppEngine Datastore to a local SQLite3
database.

Maintains an SQLite database constructed like so:

    Table <model_class_name>: ModelClassName
        id:     Automatically generated integer.
        key:    Datastore key.

    Table <model_class_name_property_name>: ModelClassName.property_name
        model_class_name_id:    model_class_name.id
        value:                  Value of property.

    View <ModelClassName>: ModelClassName
        Combined 'tabular' representation of model instances, containing a
        row for every instance and a column for every property.

        __id:           model_class_name.id
        property_name:  model_class_name_property_name.value
        ...

Invoking any command will automatically add new table definitions to the
database, if any, to the database, and recreate its views.

Fact and property table names are mapped from Python model class names
and property identifiers such that "CamelCase" becomes "camel_case," 
"dromedaryCase" becomes "dromedary_case", while "python_case" remains
unchanged.
'''

from __future__ import with_statement

import getopt
import inspect
import logging
import os
import sqlite3
import sys
import threading
import traceback

from datetime import date, datetime, time

try:
    from cStringIO import StringIO
except ImportError:
    from StringIO import StringIO


#
# AppEngine SDK related.
#

def find_sdk():
    '''
    Return the base directory for the AppEngine SDK, or None if it cannot be
    found.

    @returns        String or None.
    '''

    for path in [ '/usr/local/google_appengine' ]:
        if os.path.exists(path):
            return path


def load_appengine_modules():
    '''
    Search for the AppEngine SDK, adding its module paths to sys.path, and
    importing some important modules.

    @throws     ImportError     SDK not found, or module cannot be loaded.
    '''

    sdk_path = find_sdk()
    if not sdk_path:
        raise ImportError('cannot locate AppEngine SDK.')

    yaml_path = os.path.join(sdk_path, 'lib', 'yaml', 'lib')
    sys.path.insert(0, yaml_path)
    sys.path.insert(0, sdk_path)

    global datastore
    global datastore_types
    global db
    global users
    global remote_api_stub

    from google.appengine.api import datastore
    from google.appengine.api import datastore_types
    from google.appengine.api import users
    from google.appengine.ext import db
    from google.appengine.ext.remote_api import remote_api_stub


def init_sdk_env(app_name, email, password, remote_path='/remote_api'):
    '''
    Initialize various environment variables used by the SDK, and log into
    the application.

    @param[in]  app_name    application name, e.g. "shell".
    @param[in]  email       Developer's e-mail address.
    @param[in]  password    Password.
    @param[in]  remote_path Path to remote_api handler on server.
    '''

    os.environ['AUTH_DOMAIN'] = 'gmail.com'
    os.environ['USER_EMAIL'] = email
    remote_api_stub.ConfigureRemoteDatastore(app_name, remote_path,
                                             lambda: (email, password))

    # TODO(dmw): ensure remote_api is thread-safe.
    # 'ping' /remote_api before firing up a bunch of threads, which seems to
    # result in logging in multiple times.
    datastore.Get([db.Key.from_path('NonExistent', 1337)])


#
# Program implementation.
#

class Bag(dict):
    __getattr__ = dict.__getitem__

class ModelInfo(Bag):
    'SQL mapping information for a google.appengine.ext.db.Model subclass.'

class PropertyInfo(Bag):
    'SQL mapping information for a google.appengine.ext.db.Property instance.'


def translate_type(typ):
    '''
    Given a Python type, or one of the extended AppEngine type classes,
    return a string describing what SQL data type Datastore properties of
    this type should be mapped to.

    The type parameter comes from the Property class's data_type class
    variable, except for ReferenceProperties, where it is assumed to be Key.

    Returns a tuple whose first item is a string with the SQL data type, and
    second item is a function that when called on a value of this type,
    returns a value suitable for INSERTing with DBAPI.

    @param[in]  typ         One of appengine.ext.db._ALLOWED_PROPERTY_TYPES.
    @returns                ("SQL TYPE", translator function)
    @raises     TypeError   Type cannot be translated to SQL.
    '''

    for sql_type, rules in translate_type.map:
        for klass, translator in rules:
            if issubclass(typ, klass):
                return sql_type, translator

    raise TypeError('don\'t know how to translate type %r to SQL.' % (typ,))


def build_translate_type_map():
    '''
    Build the mappings of Datastore types to SQL types and translator
    functions. This is done inside a function because the AppEngine SDK is not
    statically imported.
    '''

    # ( 'DestSqlType' -> ( (issubclass, translator), ), )
    # When modifying, be very aware of inheritance hierarchy and effects it
    # has on the order of below.
    translate_type.map = (
        ( 'TEXT', (
            ( datastore_types.Key, lambda v: str(v) ),
            # Map 8 bit data using a codepage that defines every value.
            ( datastore_types.ByteString, lambda v: v.decode('iso8859-1') ),
            ( datastore_types.IM, lambda v: unicode(v) ),
            ( users.User, lambda v: v.email() ),
            ( datastore_types.GeoPt, lambda v: '%s:%s' % (v.lat, v.lon) ),
            ( str, lambda v: v.decode('iso8859-1') ),
            ( unicode, lambda v: v ),
            ( basestring, lambda v: unicode(v) ),
        ), ),
        ( 'TIMESTAMP', (
            ( datetime, lambda v: v and v.strftime('%Y-%m-%d %H:%M:%S') or None ),
            # TODO(dmw): what to do with these?
            ( time, lambda v: v and v.strftime('01-01-1970 %H:%M:%S') or None ),
            ( date, lambda v: v and v.strftime('%Y-%m-%d %H:%M:%S') or None ),
        ), ),
        ( 'INTEGER', (
            # int catches bool too.
            ( int, lambda v: v and long(v) or None ),
            # catching Rating too.
            ( long, lambda v: v and long(v) or None ),
        ), ),
        ( 'REAL', (
            ( float, lambda v: v ),
        ), ),
    )


def get_models(lib_paths, module_names, exclude):
    '''
    Load a set of Python modules and search them for subclasses of
    google.appengine.ext.db.Model. Before attempting imports, temporarily
    prepend the given extra library paths to sys.path.

    Filters out Model subclasses whose properties() returns an empty
    dictionary, in order to avoid helper subclasses used for adding
    functionality, but not directly used for managing entities.

    @param[in]  lib_paths       List of string filesystem paths.
    @param[in]  module_names    List of module names, possibly including
                                package prefix, e.g. "foo" or "foo.bar".
    @param[in]  exclude         List of string model subclass names to exclude.
    '''

    models = set()

    old_sys_path = sys.path
    sys.path = lib_paths + sys.path
    try:
        for name in module_names:
            module = __import__(name, None, None, ['.'])
            for obj in vars(module).itervalues():
                if inspect.isclass(obj) and issubclass(obj, db.Model):
                    klass_name = obj.__name__
                    if not obj.properties():
                        logging.debug('ignoring %s.%s: no properties.',
                                      name, klass_name)
                        continue

                    if klass_name in exclude:
                        logging.debug('ignoring %s.%s: excluded.',
                                      name, klass_name)
                        continue

                    models.add(obj)
    finally:
        sys.path = old_sys_path

    return models


def translate_name(class_name, prop_name=None):
    '''
    Translate Python style naming scheme to SQL. See module docstring. If
    property_name is given, it is translated and appended to the class name
    delimited with an underscore, i.e.

        PlaylistItem.lastUpdate -> playlist_item_last_update

    @param[in]  class_name      String class name, e.g. "PlaylistItem".
    @param[in]  prop_name       Optional string property name.
    '''

    assert isinstance(class_name, str) and class_name
    assert prop_name or (prop_name is None)

    if prop_name:
        class_name += '_' + prop_name

    output = StringIO()
    in_upper = class_name[0].isupper()

    for char in class_name:
        if char.isupper():
            if not in_upper:
                output.write('_')
                in_upper = True
            output.write(char.lower())
        else:
            output.write(char)
            in_upper = False

    return output.getvalue()


def get_model_map(models):
    '''
    Return a mapping of the given models to dictionaries containing tuples of
    information mapping their properties to SQL.

    @param[in]  models      Sequence of Model subclasses.
    @returns                List of ModelInfo objects, see code.
    '''

    infos = []

    for klass in models:
        info = ModelInfo(klass=klass, name=klass.__name__,
                         table=translate_name(klass.__name__), props=[],
                         now_prop=None)

        for prop in klass.properties().itervalues():
            prop_table_name = translate_name(info.table, prop.name)
            # TODO(dmw): seems like a bug in the SDK. data_type should be
            # Key, not Model.
            if isinstance(prop, db.ReferenceProperty):
                typ = db.Key
            else:
                typ = prop.data_type

            try:
                sql_type, translator = translate_type(typ)
            except TypeError, e:
                logging.error('%s.%s: %s', klass.__name__, prop.name, e)
                raise

                return prop

            prop_info = PropertyInfo(prop=prop, name=prop.name,
                                     table=prop_table_name,
                                     sql_type=sql_type,
                                     translator=translator)

            info.props.append(prop_info)
            if isinstance(prop, db.DateTimeProperty) and prop.auto_now:
                info.now_prop = prop_info

        infos.append(info)

    return infos


def get_tables_views(sql):
    '''
    Return a tuple of sets describing the tables and views in an SQLite
    database.

    @param[in]  sql     DBAPI connection object.
    @returns            (set-of-string-table-names, set-of-string-view-names)
    '''

    c = sql.cursor()
    tables = set(r[0] for r in c.execute('SELECT name '
                                         'FROM sqlite_master '
                                         "WHERE type = 'table'"))

    views = set(r[0] for r in c.execute('SELECT name '
                                        'FROM sqlite_master '
                                        "WHERE type = 'view'"))

    return tables, views


def sync_model(sql, infos):
    '''
    Given a database connection and mapping of Model subclasses to SQL types,
    add any missing tables and views to the database schema.

    @param[in]  sql     DBAPI connection object.
    @param[in]  infos   Output of get_model_map().
    '''

    tables, views = get_tables_views(sql)
    c = sql.cursor()

    for info in infos:
        # Update fact and property tables first.
        if info.table not in tables:
            c.execute('CREATE TABLE %s ('
                        'id PRIMARY KEY,'
                        'ds_key TEXT NOT NULL)'
                        % (info.table,))
            logging.debug('created %s for Model %s', info.table, info.name)

        for prop_info in info.props:
            if prop_info.table in tables:
                continue

            c.execute('CREATE TABLE %s ('
                        '%s_id INTEGER NOT NULL UNIQUE,'
                        'value %s'
                      ')' % (prop_info.table, info.table,
                             prop_info.sql_type))
            logging.debug('created %s for %s.%s', prop_info.table,
                                                  info.name, prop_info.name)

    # Update VIEW definitions after, in order to avoid referencing tables that
    # don't yet exit. Drop any old one first in case columns have been added or
    # removed.
    for info in infos:
        if info.table + '_view' in views:
            c.execute('DROP VIEW %s_view' % (info.table,))
            logging.debug('dropped existing view %s_view', info.table)

        fields = []
        joins = [ info.table ]

        for prop_info in info.props:
            fields.append('%s.value AS %s' %
                          (prop_info.table, translate_name(prop_info.name)))
            joins.append('%s ON(%s.%s_id = %s.id)' %
                         (prop_info.table, prop_info.table,
                          info.table, info.table))

        c.execute('CREATE VIEW %s_view AS SELECT %s FROM %s' %
                  (info.table,
                   ', '.join(fields),
                   ' LEFT JOIN '.join(joins)))
        logging.debug('created view %s_view', info.table)


def get_orphaned(sql, infos):
    '''
    Return a tuple of sets of table and view names that have no corresopnding
    Model subclasses or properties in the given set of models.

    @param[in]  sql         DBAPI connection objet.
    @param[in]  infos       Output of get_model_map().
    @returns                (orphaned-tables, orphaned-views)
    '''

    tables, views = get_tables_views(sql)

    active_tables = set()
    active_views = set()

    for info in infos:
        active_tables.add(info.table)
        active_views.add(info.table + '_view')
        for prop_info in info.props:
            active_tables.add(prop_info.table)

    return tables.difference(active_tables), \
           views.difference(active_views)


def print_orphaned(sql, infos):
    '''
    Output a list of tables and views that have no corresponding Model
    subclasses or properties in the given model_map.

    @param[in]  sql     DBAPI connection objet.
    @param[in]  infos   Output of get_model_map().
    '''

    tables, views = get_orphaned(sql, infos)

    if not (tables or views):
        logging.info('no orphans.')
        return

    if tables:
        logging.info('orphaned tables:')
        for table_name in tables:
            logging.info('  %s', table_name)

    if views:
        logging.info('orphaned views:')
        for view_name in views:
            logging.info('  %s', view_name)


def prune_orphaned(sql, infos):
    '''
    Delete any tables and views that have no corresponding Model subclasses or
    properties in the given set of models.

    @param[in]  sql     DBAPI connection object.
    @param[in]  infos   Output of get_model_map().
    '''

    tables, views = get_orphaned(sql, infos)
    c = sql.cursor()

    for table_name in tables:
        c.execute('DROP TABLE ' + table_name)
        logging.info('Dropped %s', table_name)

    for view_name in views:
        c.execute('DROP VIEW ' + view_name)
        logging.info('Dropped %s', view_name)

    logging.info('deleted %d objects total.', sum(map(len, [tables, views])))


def get_highest_date(sql, info):
    '''
    Fetch the highest recorded auto_now date from the given table. If no date
    can be found, just return a really old date instead.

    @param[in]  sql         DBAPI connection object.
    @param[in]  info        ModelInfo instance.
    @returns                datetime.datetime instance.
    '''

    assert info.now_prop

    # TODO(dmw): make this not do a scan.
    c = sql.cursor()

    highest = datetime(1970, 1, 1)
    for value, in c.execute('SELECT value AS value FROM %s'
                            % (info.now_prop.table,)):
        highest = max(highest, value)

    return highest


def get_highest_key(sql, info):
    '''
    Fetch the highest recorded key from the given table. If no key can be
    found, returns None.

    @param[in]  sql         DBAPI connection object.
    @param[in]  info        ModelInfo instance.
    @returns                appengine.ext.db.Key instance or None.
    '''

    # TODO(dmw): make this not do a scan.
    c = sql.cursor()

    highest = None
    for ds_key, in c.execute('SELECT ds_key FROM ' + info.table):
        key = db.Key(ds_key)
        highest = max(highest or key, key)

    return highest


def fetch_one_col(c, fmt, *args):
    for value, in c.execute(fmt, args):
        return value


def save_entity(sql, info, entity):
    '''
    Delete any existing entity from the database with the same key, then save
    the given entity.

    @param[in]  info        Associated ModelInfo instance.
    @param[in]  entity      appengine.ext.db.Model instance.
    '''

    c = sql.cursor()
    key = entity.key()
    old_id = fetch_one_col(c, 'SELECT id FROM %s WHERE ds_key = ?'
                               % (info.table, ), str(key))

    if old_id is not None:
        c.execute('DELETE FROM %s WHERE id = ?' % (info.table,), (old_id,))
        logging.debug('deleted old row from %s id=%s', info.table, old_id)

    c.execute('INSERT INTO %s(ds_key) VALUES(?)' % (info.table,), (str(key),))
    new_id = c.lastrowid

    for prop in info.props:
        if old_id is not None:
            c.execute('DELETE FROM %s WHERE %s_id = ?'
                      % (prop.table, info.table), (old_id, ))
        value = prop.translator(prop.prop.get_value_for_datastore(entity))
        c.execute('INSERT INTO %s(%s_id, value) VALUES(?, ?)'
                  % (prop.table, info.table), (new_id, value))

    return old_id is not None


def save_entities(sql, info, entities):
    '''
    Save a set of Model instances retrieved from Datastore to the database,
    possibly after deleting existing rows from the database with that share the
    same key. Also update info.highest to include the highest seen key or date.

    @param[in]  info        Associated ModelInfo instance.
    @param[in]  entities    List of Model instances.
    '''

    c = sql.cursor()
    c.execute('BEGIN')

    added = 0
    updated = 0

    for entity in entities:
        if save_entity(sql, info, entity):
            updated += 1
        else:
            added += 1

        if info.now_prop:
            candidate = info.now_prop.prop.get_value_for_datastore(entity)
            info.highest = max(info.highest or candidate, candidate)
        else:
            info.highest = max(info.highest or entity.key(), entity.key())

    c.execute('COMMIT')
    return added, updated


def fetch_thread(sql_factory, get_next, batch_size):
    '''
    Fetch worker thread. Calls get_next() to get the next Model subclass
    requiring replication, then repeatedly fetches small batches until no more
    entities remain.

    Thread exits when get_next() returns None.

    @param[in]  sql_factory     DBAPI connection factory.
    @param[in]  get_next        Callback to invoke to get next table.
    @param[in]  batch_size      Number entities to fetch per request.
    '''

    sql = sql_factory()
    info = None
    added = 0
    updated = 0

    while True:
        info = get_next(info, added, updated)
        if not info:
            break

        added = 0
        updated = 0
        logging.debug('beginning to process %s entities.', info.name)

        while True:
            query = info.klass.all()
            if info.now_prop:
                query.order(info.now_prop.name)
                query.filter(info.now_prop.name + ' >', info.highest)
            else:
                query.order('__key__')
                if info.highest:
                    query.filter('__key__ >', info.highest)

            entities = query.fetch(batch_size)
            if not entities:
                break

            logging.debug('%s: got a batch of %d', info.name, len(entities))
            added, updated = save_entities(sql, info, entities)
            logging.debug('%s: added %d, updated %d.', info.name,
                          added, updated)

    logging.debug('thread exiting; no more work.')


def fetch(sql_factory, infos, worker_count, batch_size):
    '''
    Fetch data from the AppEngine Datastore via remote_api and save it to the
    database. Synchronization happens differently depending on the properties
    of the particular Model subclass:

        * For subclasses with a DateTimeProperty whose auto_now member is True,
          query the database for the maximum value of that property, then
          iteratively fetch updated entities using an index query.

        * For other subclasses, query the database for the highest __key__
          value, then iteratively fetch entities with a higher __key__ value
          using an index query.

    @param[in]  sql_factory     DBAPI connection factory.
    @param[in]  infos           Output of get_model_map().
    @param[in]  worker_count    Number of worker threads to use.
    @param[in]  batch_size      Number entities to fetch per request.
    '''

    sql = sql_factory()
    sync_model(sql, infos)

    lock = threading.Lock()
    to_check = infos[:]
    end_event = threading.Event()
    end_count = [0]
    stats = dict(added=0, updated=0)

    logging.debug('got %d tables to check.', len(to_check))

    def get_next(last_info, added, updated):
        with lock:
            stats['added'] += added
            stats['updated'] += updated
            if added or updated:
                logging.info('%s done. Overall status: %s added, %s updated.',
                             last_info.name, stats['added'], stats['updated'])
            if to_check:
                return to_check.pop(-1)

    def safe_fetch_thread(*args):
        try:
            fetch_thread(*args)
        except:
            traceback.print_exc()

        with lock: end_count[0] += 1
        if end_count[0] == worker_count:
            end_event.set()

    for i in range(worker_count):
        thread = threading.Thread(target=safe_fetch_thread,
                                  args=(sql_factory, get_next, batch_size))
        thread.start()

    end_event.wait()
    logging.info('grand total: %s added, %s updated.',
                 stats['added'], stats['updated'])
    logging.debug('all fetch threads done; finished.')



#
# Command line interface.
#

def usage(msg=None):
    sys.stderr.write(
        'Usage: %s <command> [options]\n'
        'Options:\n'
        '\n'
        '  -a <name>    AppEngine application name, e.g. "shell"\n'
        '  -e <addr>    Developer\'s e-mail address\n'
        '  -p <pw>      Developer\'s password\n'
        '  -r <path>    remote_api path on server (default "/remote_api")\n'
        '  -L <path>    Prepend extra path to module search path\n'
        '  -m <name>    Load Model classes from module\n'
        '  -d <path>    Local database path (default "./models.sqlite3")\n'
        '  -x <name>    Exclude the given Module class\n'
        '  -N <count>   Number of fetch worker threads (default: 10)\n'
        '  -C <count>   Number of entities to fetch per request (default: 50)\n'
        '  -v           Verbose/debug output\n'
        '\n'
        '  fetch\n'
        '    Start fetching data from Datastore to local database.\n'
        '    Automatically runs "sync" if required.\n'
        '\n'
        '  orphaned\n'
        '    List properties and tables that no longer have associated\n'
        '    definitions in the loaded Model classes.\n'
        '\n'
        '  prune\n'
        '    Remove properties and tables from local database that no\n'
        '    longer have associated definitions in the loaded Model\n'
        '    classes. Check "orphaned" output first to verify this\n'
        '    won\'t result in data loss!\n'
        '\n'
        'Examples:\n'
        '    Load Models from $HOME/src/myapp/{models,counter}.py to\n'
        '    create/update the schema in $HOME/myapp.db:\n'
        '\n'
        '        %s -L $HOME/src -m myapp.models -m myapp.counters\n'
        '            -d $HOME/myapp.db sync\n'
        '\n'
        '    Backup "myapp.appspot.com"\'s datastore to $HOME/myapp.db\n'
        '    except for RemoteUrlCacheEntry:\n'
        '\n'
        '        %s -L $HOME/src -m myapp.models -m myapp.counters \\\n'
        '            -d $HOME/myapp.db -x RemoteUrlCacheEntry \\\n'
        '            -a myapp -e me@gmail.com -p 1234 \\\n'
        '            fetch\n'
        '\n'

        % (sys.argv[0], sys.argv[0], sys.argv[0])
    )

    if msg:
        sys.stderr.write('Error: %s\n' % (msg,))


def main():
    '''
    CLI implementation.
    '''

    try:
        load_appengine_modules()
    except ImportError:
        usage('could not locate AppEngine SDK modules. Traceback below.')
        traceback.print_last()

    app_name = None
    email = None
    password = None
    remote_path = '/remote_api'
    lib_paths = []
    model_modules = []
    sql_path = './models.sqlite3'
    exclude_models = []
    level = logging.INFO
    worker_count = 10
    batch_size = 50

    try:
        optlist = 'a:e:p:r:L:m:d:x:vN:C:'
        opts, args = getopt.gnu_getopt(sys.argv[1:], optlist)
    except getopt.GetoptError, e:
        usage(str(e))
        return 1

    for opt, optarg in opts:
        if opt == '-a':
            app_name = optarg
        elif opt == '-e':
            email = optarg
        elif opt == '-p':
            password = optarg
        elif opt == '-r':
            remote_path = optarg
        elif opt == '-L':
            lib_paths.append(optarg)
        elif opt == '-m':
            model_modules.append(optarg)
        elif opt == '-d':
            sql_path = optarg
        elif opt == '-x':
            exclude_models.append(optarg)
        elif opt == '-v':
            level = logging.DEBUG
        elif opt == '-N':
            try:
                worker_count = int(optarg, 10)
                if worker_count < 1:
                    raise ValueError('must be >= 1')
            except ValueError, e:
                usage('Bad -N: ' + str(e))
                return 1
        elif opt == '-C':
            try:
                batch_size = int(optarg, 10)
                if batch_size < 1:
                    raise ValueError('must be >= 1')
            except ValueError, e:
                usage('Bad -C: ' + str(e))
                return 1
        else:
            assert False

    logging.basicConfig(level=level)

    if len(args) > 1:
        usage('too many arguments: please specify a single command.')
        return 1
    elif len(args) == 0:
        usage('please specify a command.')
        return 1
    command = args[0]

    if command not in ('sync', 'fetch', 'orphaned', 'prune'):
        usage('unrecognized command %r specified.' % (command,))
        return 1

    if not model_modules:
        usage('no model modules specified, at least one required.')
        return 1

    models = get_models(lib_paths, model_modules, exclude_models)
    if not models:
        logging.error('no google.appengine.ext.db.Model subclasses found '
                      'in %s', model_modules)
        return 1

    # Initialize remote_api before opening database (avoids creating a junk
    # DB on disk after a failed run).
    if command == 'fetch':
        if not (app_name and email and password and remote_path):
            usage('a required parameter is missing.')
            return 1
        init_sdk_env(app_name, email, password, remote_path)

    # SQLite3 requires one connection per thread, I require logging.
    def sql_factory():
        class LoggingCursor(sqlite3.Cursor):
            def execute(self, fmt, args=None):
                try:
                    if args:
                        return sqlite3.Cursor.execute(self, fmt, args)
                    else:
                        return sqlite3.Cursor.execute(self, fmt)
                except:
                    logging.error('failed sql was: %s %s', fmt, args)
                    raise

        class LoggingConnection(sqlite3.Connection):
            def cursor(self):
                return sqlite3.Connection.cursor(self, LoggingCursor)

        return sqlite3.connect(sql_path, isolation_level=None,
                               factory=LoggingConnection,
                               detect_types=sqlite3.PARSE_DECLTYPES)


    # Initialize the database connection.
    try:
        sql = sql_factory()
    except sqlite3.OperationalError, e:
        logging.error('could not open database: %s', e)
        return 1

    # Perform any common initializations here.
    build_translate_type_map()
    infos = get_model_map(models)
    sync_model(sql, infos)
    for info in infos:
        if info.now_prop:
            info.highest = get_highest_date(sql, info)
        else:
            info.highest = get_highest_key(sql, info)

    # Local-only commands:
    if command == 'orphaned':
        print_orphaned(sql, infos)
    elif command == 'prune':
        prune_orphaned(sql, infos)
    elif command == 'fetch':
        fetch(sql_factory, infos, worker_count, batch_size)
    else:
        assert False


if __name__ == '__main__':
    sys.exit(main() or 0)
