all: watcher.svg

%.svg: %.dot
	dot -Tsvg $^ > $@
