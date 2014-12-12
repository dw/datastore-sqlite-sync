This self-contained tool enables incremental synchronization of your data from
<a href="http://code.google.com/appengine/docs/python/datastore/">Google
App Engine's Datastore</a> to a local <a href="http://www.sqlite.org/">SQLite 3
database</a>. It will automatically convert your model definitions into an SQL
schema, and download the model data in parallel using the new <tt><a
href="http://code.google.com/appengine/articles/remote_api.html">remote_api</a></tt>.

_Synchronization is currently unidirectional_ (i.e. Datastore to SQLite, not
the other way around) due to a lack of need, and also at least one technical
limitation.


## Introduction

There are still many data processing tasks that aren't possible on App Engine,
to which a traditional SQL database is ideally suited. These include driving a
full text indexer, running reports that aggregate complex statistics in
multiple dimensions from your data, or asking ad-hoc questions that your
application's counters weren't designed to support.

This utility solves these problems, while enabling many more applications to
integrate with your data with minimal time and effort. An SQL schema is
automatically generated by introspecting the model classes defined in your
application's source code, into which new and updated entities are
automatically fetched with a single command.

The database may be used for running interactive queries using one of the many
<a href="http://www.sqlite.org/cvstrac/wiki?p=ManagementTools">free GUI
management tools</a>, or even hooking up to <a
href="http://www.ch-werner.de/sqliteodbc/">Microsoft Excel via ODBC</a>.
Additionally, by configuring a cron job it is possible to mirror your entire
Datastore to an external location, for consumption by external software (for
example, full text indexing, automated reporting and analysis, etc.)


## How This Works

The magic <tt><a
href="http://code.google.com/appengine/docs/python/datastore/queriesandindexes.html#Queries_on_Keys">__key__</a></tt>
property is used to search for new immutable entities, while any Model
subclasses that define at least one <a
href="http://code.google.com/appengine/docs/python/datastore/typesandpropertyclasses.html#DateTimeProperty">DateTimeProperty</a>
with `auto_now=True` will be automatically re-fetched every time they are
modified. *This means that you gain completely hands-free replication to an
effortlessly accessible SQL database* simply by including a single
`DateTimeProperty` in each of your mutable models.


## Model → SQL Schema Mapping

All identifiers are mapped like so: `ModelClassName` → `model_class_name`, and `ModelClassName.propertyName` → `model_class_name_property_name`.

The current code generates the following SQL objects:

 * One `TABLE` for each <tt><a href="http://code.google.com/appengine/docs/python/datastore/modelclass.html">Model</a></tt> subclass, containing a unique integer (`id`) and string-encoded Datastore <a href="http://code.google.com/appengine/docs/python/datastore/keyclass.html">Key</a>.

 * One `TABLE` for each property of each Model, containing an integer (`class_name_id`) and the actual value column (`value`).

 * One `VIEW` for each Model, defined as a `SELECT` which joins together all the other tables into a single combined "SQL like" table. This is the most useful object.

This design was chosen to make it trivial to add and drop columns on large data sets, without having to wait for large `ALTER TABLE` commands to run. It also makes it easier to define custom `VIEW`s on just the subset of your data you need.

## Type Mapping

<table>
<tr>
<th>SQL Type
<th>Datastore Native Type

<tr>
<td><tt>TEXT</tt>
<td>Key, ByteString, IM, User, GeoPt, PhoneNumber, Email, etc. (all simple text fields)

<tr>
<td><tt>TIMESTAMP</tt>
<td>datetime, date, time

<tr>
<td><tt>INTEGER</tt>
<td>int, long, Rating

<tr>
<td><tt>REAL</tt>
<td>float
</table>


## Example

The following model:

````python
class Address(db.Model):
    careOf = db.StringProperty()
    line1 = db.StringProperty()
    line2 = db.StringProperty()
    lastUpdated = db.DateTimeProperty(auto_now=True)
````

Would be mapped to:

````sql
CREATE TABLE address_entity(id INTEGER PRIMARY KEY, ds_key TEXT NOT NULL);

CREATE TABLE address_care_of(address_entity_id INT NOT NULL, value TEXT);
CREATE TABLE address_line1(address_entity_id INT NOT NULL, value TEXT);
CREATE TABLE address_line2(address_entity_id INT NOT NULL, value TEXT);
CREATE TABLE address_last_updated(address_entity_id INT NOT NULL, value TIMESTAMP);

CREATE UNIQUE INDEX address_entity_ds_key_index
    ON address_entity(ds_key);
CREATE UNIQUE INDEX address_care_of_address_entity_id_index
    ON address_care_of(address_entity_id);
CREATE UNIQUE INDEX address_line1_address_entity_id_index 
    ON address_line1(address_entity_id);
CREATE UNIQUE INDEX address_line2_address_entity_id_index 
    ON address_line2(address_entity_id);
CREATE UNIQUE INDEX address_last_updated_address_entity_id_index
    ON address_last_updated(address_entity_id);

CREATE VIEW address AS
SELECT
    address_entity.id AS __id,
    address_entity.ds_key AS __ds_key,
    address_care_of.value AS care_of,
    address_line1.value AS line1,
    address_line2.value AS line2,
    address_last_updated.value AS last_updated
FROM
    address_entity
    LEFT JOIN address_care_of ON (address_care_of.address_entity_id = address_entity.id)
    LEFT JOIN address_line1 ON (address_line1.address_entity_id = address_entity.id)
    LEFT JOIN address_line2 ON (address_line2.address_entity_id = address_entity.id)
    LEFT JOIN address_last_updated ON (address_last_updated.address_entity_id = address_entity.id)

-- Example query:
SELECT COUNT(\*) FROM address WHERE line1 LIKE '1 Infinite Loop%'
````


## Usage

````
Usage: dsync.py <command> [options]
Options:

  -a <name>    App Engine application name, e.g. "shell"
  -e <addr>    Developer's e-mail address (default: prompt)
  -p <pw>      Developer's password (default: prompt)
  -r <path>    remote_api path on server (default "/remote_api")
  -L <path>    Prepend extra path to module search path
  -m <name>    Load Model classes from module
  -d <path>    Local database path (default "./models.sqlite3")
  -x <name>    Exclude the given Model class
  -N <count>   Number of fetch worker threads (default: 5)
  -C <count>   Number of entities to fetch per request (default: 50)
  -v           Verbose/debug output

  --batch      Fail rather than prompt for a password if none is
               provided on the command line.

  --sdk-path=<path>
               Path to App Engine SDK (default: search).

  --trigger-cmd="<ModelGlob>:command"
               Arrange for the given system command to be executed
               after new or updated entities whose class matches
               ModelGlob fetched (glob may contain * and ?).

  --trigger-sql="<ModelGlob>:SQL STATEMENT"
               Arrange for the given SQL statement to be executed
               after new or updated entities whose class matches
               ModelGlob fetched (glob may contain * and ?).

  --help       This message.

Commands:

  sync-model
    Synchronize the database schema to match the loaded Model
    subclasses.

  fetch
    Start fetching data from Datastore to the database,
    synchronizing its schema if necessary.

  orphaned
    List properties and tables that no longer have associated
    definitions in the loaded Model classes.

  prune
    Remove properties and tables from local database that no
    longer have associated definitions in the loaded Model
    classes. Check "orphaned" output first to verify this
    won't result in data loss!

Example:
    Backup "myapp.appspot.com"'s datastore to $HOME/myapp.db
    except for RemoteUrlCacheEntry:

        dsync.py -L $HOME/src -m myapp.models -m myapp.counters  \
            -d $HOME/myapp.db -x RemoteUrlCacheEntry       \
            -a myapp -e me@gmail.com -p 1234               \
            fetch
````


## Known Issues

This code represents about 10 hours worth of work; it's still at a very early
stage. Please see the <a
href="http://code.google.com/p/datastore-sqlite-sync/issues/list">issue
tracker</a> for a more definitive list of issues, but most importantly right
now:

 * With high worker thread counts, SQLite locks timeout.
 * Not well tested.
 * Only supports SQLite; PostgreSQL support would be great for very large data sets.

I will be productionizing the code in the coming months, but if you come across a major issue, please tell me about it.



## Configuration

### Local System

Before using the utility, you must have Python 2.5 and the <a
href="http://code.google.com/appengine/downloads.html">Google App Engine SDK</a>
installed on your working machine, along with a copy of your site's source
code. The source code is currently necessary for introspecting your
application's Datastore schema.

The utility searches for the SDK in the default locations for Windows and OS X.
If you have changed the install path for the SDK, you will need to specify it
using a command line parameter.

After completing these steps, you must configure a `remote_api` URI for your
site as shown below.


### Application Changes

Simply add the following to <a
href="http://code.google.com/appengine/docs/python/tools/configuration.html">app.yaml</a>
in your project directory:

````yaml
handlers:  
  - url: /remote_api
    script: $PYTHON_LIB/google/appengine/ext/remote_api/handler.py
    login: admin
````

It is recommended that you use the URI shown above, however you can specify an
alternative using a command-line parameter if you desire. This enables the
`remote_api` handler built into App Engine, which you can <a
href="http://code.google.com/appengine/articles/remote_api.html">read more
about here</a>.


### Creating A Sync Script

It is recommended that you create a batch file or UNIX shell script to save the
settings used for launching the utility. This helps reduce the potential for
human error cropping up (for example, missing a library path).

The main tasks required for this are picking a stable location for your site's
source code, say, `$HOME/src/my-site` (or `%USERPROFILE%\my-site` for Windows
users), and figuring out which modules in your source code contain Datastore
model definitions. This will be easier if you use only a single file for
declaring models.

Here is an example sync script written in bash. It will prompt for
<tt>me@gmail.com</tt>'s password at startup, or you can hard-code it using the
<tt>-p</tt> option.

````bash
#!/bin/bash

EMAIL=me@gmail.com
APPNAME=mysite           # mysite.appspot.com
SOURCE_DIR=$HOME/src/my-site
DATABASE_PATH=$HOME/data/my-site.sqlite3

TRIG="Member:$HOME/bin/index-new-members.sh"

dsync.py \
    -L $SOURCE_DIR         \
    -m my_site.models      \ # Equivalent to $SOURCEDIR/my_site/models.py 
    -m my_site.counter     \
    -a $APPNAME            \
    -e $EMAIL              \
    -N 5                   \ # Start 5 worker threads.
    --trigger-cmd="$TRIG"  \ # Trigger indexing when a new member joins.
    fetch
````


### Start Syncing

````bash
$ ./my-sync-script.sh
INFO:root:Server: my-site.appspot.com
INFO:root:Session done: 1 added, 0 updated.
INFO:root:Room done: 1 added, 0 updated.
INFO:root:Invitation done: 2 added, 0 updated.
INFO:root:Video done: 5 added, 0 updated.
INFO:root:Item done: 5 added, 0 updated.
INFO:root:Member done: 2 added, 0 updated.
INFO:root:grand total: 1.73s for 16 added, 0 updated in 13 models.
$
$ ./my-sync-script.sh
INFO:root:Server: my-site.appspot.com
INFO:root:grand total: 0.97s for 0 added, 0 updated in 13 models.
````

If all has gone well, you should now have a local SQLite copy of your Datastore!


### Run Some Queries

````
$ sqlite3 $HOME/data/my-site.sqlite3
SQLite version 3.5.7
Enter ".help" for instructions
sqlite> .mode column
sqlite> SELECT COUNT(*) FROM session;
COUNT(*)  
----------
1         
sqlite> SELECT session_id, display_name, last_seen, last_address, expiry_time, first_seen FROM session;
session_id                        display_name  last_seen            last_address    expiry_time  first_seen         
--------------------------------  ------------  -------------------  --------------  -----------  -------------------
0ed373e4a697d2fed5b7e6b00f462423  Anonymous     2009-02-24 15:02:45  80.127.152.220               2009-02-24 12:16:03
````