#!/usr/bin/env python2.5

'''
Synchronize the contents of a Google AppEngine Datastore to a local SQLite3
database.

Maintains an SQLite database constructs like so:

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

Fact and property table names are mapped from Python model class names
and property identifiers such that "CamelCase" becomes "camel_case," 
"dromedaryCase" becomes "dromedary_case", and "python_case" remains the
unchanged. For convenience, view names are not translated.
'''

import getopt
import inspect
import logging
import os
import sqlite3
import sys
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

    global datastore_types
    global users
    global db
    global remote_api_stub

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
    ov.environ['USER_EMAIL'] = email
    remote_api_stub.ConfigureRemoteDatastore(app_name, remote_path,
                                             lambda: (email, password))


#
# Program implementation.
#

def translate_type(typ):
    '''
    Given a Python type, or one of the extended AppEngine type classes,
    return a string describing what SQL data type Datastore properties of
    this type should be mapped to.

    The type parameter comes from the Property class's data_type class
    variable.

    Returns a tuple whose first item is a string with the SQL data type, and
    second item is a function that when called on a value of this type,
    returns a value suitable for INSERTing with DBAPI.

    @param[in]  typ         One of appengine.ext.db._ALLOWED_PROPERTY_TYPES.
    @returns                ("SQL TYPE", translator function)
    @raises     TypeError   Type cannot be translated to SQL.
    '''

    for sql_type, rules in translate_type.model_map:
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
    translate_type.model_map = (
        ( 'TEXT', (
            ( datastore_types.Key, lambda v: str(v) ),
            # model_map 8 bit data using a codepage that defines every value.
            ( datastore_types.ByteString, lambda v: v.decode('iso8859-1') ),
            ( datastore_types.IM, lambda v: unicode(v) ),
            ( users.User, lambda v: v.email() ),
            ( datastore_types.GeoPt, lambda v: '%s:%s' % (v.lat, v.lon) ),
            ( str, lambda v: v.decode('iso8859-1') ),
            ( unicode, lambda v: v ),
            ( basestring, lambda v: unicode(v) ),
        ), ),
        ( 'DATETIME', (
            ( datetime, lambda v: v.strftime('%Y-%m-%d %H:%M:%S') ),
            # TODO(dmw): what to do with these?
            ( time,     lambda v: v.strftime('01-01-1970 %H:%M:%S') ),
            ( date,     lambda v: v.strftime('%Y-%m-%d %H:%M:%S') ),
        ), ),
        ( 'INTEGER', (
            # int catches bool too.
            ( int, lambda v: long(v) ),
            # catching Rating too.
            ( long, lambda v: long(v) ),
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
                        logging.debug('ignoring %s from module %s: no properties.',
                                      klass_name, name)
                        continue

                    if klass_name in exclude:
                        logging.debug('ignoring %s from module %s: excluded.',
                                      klass_name, name)
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
    @returns                Complex structure. See code.
    '''

    model_map = {}

    for klass in models:
        table_name = translate_name(klass.__name__)
        props = {}

        for prop_name, prop in klass.properties().iteritems():
            prop_table_name = translate_name(table_name, prop_name)
            # TODO(dmw): seems like a bug in the SDK. data_type should be
            # Key, not Model.
            if isinstance(prop, db.ReferenceProperty):
                typ = db.Key
            else:
                typ = prop.data_type

            try:
                sql_type, translator = translate_type(typ)
            except TypeError, e:
                logging.error('%s.%s: %s', klass.__name__, prop_name, e)
                raise

            props[prop_name] = prop, prop_table_name, sql_type, translator

        model_map[klass.__name__] = klass, table_name, props

    return model_map


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


def sync_model(sql, model_map):
    '''
    Given a database connection and mapping of Model subclasses to SQL types,
    add any missing tables and views to the database schema.

    @param[in]  sql         DBAPI connection object.
    @param[in]  model_map   Model mapping created by get_model_map().
    '''

    tables, views = get_tables_views(sql)
    c = sql.cursor()

    # Update fact and property tables first.
    for klass_name, (klass, table_name, props) in model_map.iteritems():
        if table_name not in tables:
            c.execute('CREATE TABLE %s(id INT NOT NULL)' % (table_name,))
            logging.info('created %s for Model %s', table_name, klass_name)

        for prop_name, bits in props.iteritems():
            prop, prop_table_name, sql_type, translator = bits
            if prop_table_name in tables:
                continue

            c.execute('CREATE TABLE %s ('
                        '%s_id INTEGER NOT NULL UNIQUE,'
                        'value %s'
                      ')' % (prop_table_name, table_name, sql_type))
            logging.info('created %s for %s.%s', prop_table_name,
                                                 klass_name, prop_name)

        # Update VIEW definitions. Drop the old one first in case any columns
        # have been added or removed.
        if table_name + '_view' in views:
            c.execute('DROP VIEW %s_view' % (table_name,))
            logging.debug('dropped existing view %s_view', table_name)

        fields = []
        joins = [ table_name ]

        for prop_name, bits in props.iteritems():
            prop, prop_table_name, sql_type, translator = bits
            fields.append('%s.value AS %s' %
                          (prop_table_name, translate_name(prop_name)))
            joins.append('%s ON(%s.%s_id = %s.id)' %
                         (prop_table_name, prop_table_name,
                          table_name, table_name))

        c.execute('CREATE VIEW %s_view AS SELECT %s FROM %s' %
                  (table_name,
                   ', '.join(fields),
                   ' LEFT JOIN '.join(joins)))
        logging.info('created view %s_view', table_name)


def get_orphaned(sql, model_map):
    '''
    Return a tuple of sets of table and view names that have no corresopnding
    Model subclasses or properties in the given model_map.

    @param[in]  sql         DBAPI connection objet.
    @param[in]  model_map   Model mapping created by get_model_map().
    @returns                (orphaned-tables, orphaned-views)
    '''

    tables, views = get_tables_views(sql)

    active_tables = set()
    active_views = set()

    for _, (_, table_name, props) in model_map.iteritems():
        active_tables.add(table_name)
        active_views.add(table_name + '_view')
        for _, table_name, _, _ in props.itervalues():
            active_tables.add(table_name)

    return tables.difference(active_tables), \
           views.difference(active_views)


def print_orphaned(sql, model_map):
    '''
    Output a list of tables and views that have no corresponding Model
    subclasses or properties in the given model_map.

    @param[in]  sql         DBAPI connection objet.
    @param[in]  model_map   Model mapping created by get_model_map().
    '''

    tables, views = get_orphaned(sql, model_map)

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


def prune_orphaned(sql, model_map):
    '''
    Delete any tables and views that have no corresponding Model subclasses or
    properties in the given model_map.

    @param[in]  sql         DBAPI connection objet.
    @param[in]  model_map   Model mapping created by get_model_map().
    '''

    tables, views = get_orphaned(sql, model_map)
    c = sql.cursor()

    for table_name in tables:
        c.execute('DROP TABLE ' + table_name)
        logging.info('Dropped %s', table_name)

    for view_name in views:
        c.execute('DROP VIEW ' + view_name)
        logging.info('Dropped %s', view_name)

    logging.info('deleted %d objects total.', sum(map(len, [tables, views])))


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
        '  -v           Verbose/debug output\n'
        '\n'
        'Commands:\n'
        '  sync\n'
        '    Create local database if it does not exist, then add or\n'
        '    update its tables and views with any newly discovered\n'
        '    model properties.\n'
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
        '            -d $HOME/myapp.db -x RemoteUrlCacheEntry\\\n'
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

    try:
        optlist = 'a:e:p:r:L:m:d:x:v'
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

    # Perform any common initializations here.
    build_translate_type_map()
    model_map = get_model_map(models)

    # Initialize the database connection.
    try:
        sql = sqlite3.connect(sql_path)
    except sqlite3.OperationalError, e:
        logging.error('could not open database: %s', e)
        return 1

    # Local-only commands:
    if command == 'sync':
        sync_model(sql, model_map)
    elif command == 'orphaned':
        print_orphaned(sql, model_map)
    elif command == 'prune':
        prune_orphaned(sql, model_map)
    elif command == 'fetch':
        fetch(sql, model_map)
    else:
        assert False


if __name__ == '__main__':
    sys.exit(main() or 0)
