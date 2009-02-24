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
        Combined 'tabular' representation of model instances, containing a row
        for every instance and a column for every property.

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

def get_models(lib_paths, module_names):
    '''
    Load a set of Python modules and search them for subclasses of
    google.appengine.ext.db.Model. Before attempting imports, temporarily
    prepend the given extra library paths to sys.path.

    @param[in]  lib_paths       List of string filesystem paths.
    @param[in]  module_names    List of module names, possibly including
                                package prefix, e.g. "foo" or "foo.bar".
    '''

    models = set()

    old_sys_path = sys.path
    sys.path = lib_paths + sys.path
    try:
        for name in module_names:
            module = __import__(name, None, None, ['.'])
            for obj in vars(module).itervalues():
                if inspect.isclass(obj) and issubclass(obj, db.Model):
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


def translate_type(typ):
    '''
    Given a Python type, or one of the extended AppEngine type classes, return
    a string describing what SQL data type Datastore properties of this type
    should be mapped to.

    The type parameter comes from the Property class's data_type class
    variable.

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

# ( 'DestSqlType' -> ( ( issubclass, translator ) ) )
# When modifying, be very aware of inheritance hierarchy and effects it has on
# the order of below.
translate_type.map = (
    ( 'TEXT',
        ( datastore_types.Key,        lambda v: str(v)                   ),
        # Map 8 bit data using a codepage that defines every value.
        ( datastore_types.ByteString, lambda v: v.decode('iso8859-1')    ),
        ( datastore_types.IM,         lambda v: unicode(v)               ),
        ( users.User,                 lambda v: v.email()                ),
        ( datastore_types.GeoPt,      lambda v: '%s:%s' % (v.lat, v.lon) ),
        ( str,                        lambda v: v.decode('iso8859-1')    ),
        ( unicode,                    lambda v: v                        ),
    ),
    ( 'DATETIME',
        ( datetime,                   lambda v: v.strftime(
                                                   '%Y-%m-%d %H:%M:%S')  ),
        ( time,                       lambda v: v.strftime(
                                                   '01-01-1970 %H:%M:%S')),
        ( date,                       lambda v: v.strftime(
                                                   '%Y-%m-%d %H:%M:%S')  ),
    ),
    ( 'INTEGER',
        # int catches bool too.
        ( int,                        lambda v: long(v)                  ),
        # catching Rating too.
        ( long,                       lambda v: long(v)                  ),
    ),
    ( 'REAL',
        ( float,                      lambda v: v                        ),
    )
)


def sync_model(db, models):
    '''
    Given a list of 
    '''

    c = db.cursor()

    tables = set(c.execute('SELECT name '
                           'FROM sqlite_master '
                           "WHERE type = 'table'"))
    views = set(c.execute('SELECT name '
                          'FROM sqlite_master '
                          "WHERE type = 'view'").fetchall())

    # Update fact and property tables first.
    new_fact_tables = []
    new_prop_tables = []

    for klass in models:
        table = translate_name(klass.__name__)
        if table not not tables:
           new_fact_tables.append((klass, table))

        for prop_name, prop in klass.properties().iteritems():
            table = translate_name(klass.__name__, prop_name)
            if table not in tables:
                new_prop_tables_append((klass, prop_name, prop, table))

    logging.info('About to create %d fact tables and %d property tables.',
                 len(new_fact_tables), len(new_prop_tableS))

    for klass, table in new_fact_tables:
        c.execute('CREATE TABLE %s(id INT NOT NULL)' % (table,))
        logging.info('-- created %s for Model %s', table, klass.__name__)

    for klass, prop_name, prop, table in new_prop_tables:
        try:
            sql_type, translator = translate_type(prop.data_type)
        except TypeError, e:
            logging.error('unable to create property table for %s.%s: %s',
                          klass.__name__, prop_name, e)
            db.rollback()
            raise SystemExit(1)

        

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
        '            -a myapp -e dw@botanicus.net -p 1234 \\\n'
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
    db_path = './models.sqlite3'
    exclude_models = []

    try:
        optlist = 'a:e:p:r:L:m:d:x:'
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
            db_path = optarg
        elif opt == '-x':
            exclude_models.append(optarg)
        else:
            assert False

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

    models = get_models(lib_paths, model_modules)
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

    # Initialize the database connection.
    try:
        db = sqlite3.connect(db_path)
    except sqlite3.OperationalError, e:
        logging.error('could not open database: %s', e)
        return 1

    # Local-only commands:
    if command == 'sync':
        sync_model(db, models)
    elif command == 'orphaned':
        print_orphaned(db, models)
    elif command == 'prune':
        prune_orphaned(db, models)
    elif command == 'fetch':
        fetch(db, models)
    else:
        assert False


if __name__ == '__main__':
    sys.exit(main() or 0)
