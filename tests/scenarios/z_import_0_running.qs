# A folder of pages in grimoire/import/ that takes a while to import (the job is slowed down, as a
# book's is on the Scribe): while it runs, the Library says it is importing, so a list that stays as
# it was is not taken for an import that failed. The moment the job is done the notebook is in the
# list, without leaving the screen.
# copy: tests/fixtures/scen-import import
# env: GRIMOIRE_BG_DELAY_MS=3000
# rust-only
expect screen is library
expect toast is Importing pages into Grimoire...
expect library.items is 0
wait 1200
shot 01-importing
expect toast is Importing pages into Grimoire...
expect library.items is 0
waitbg
wait 300
shot 02-imported
expect library.items is 1
expect toast is Imported a notebook of 3 pages.
quit
