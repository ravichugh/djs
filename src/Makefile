
LIBS=-libs unix,str
LAM=-I LamJS
STATS=-I BNstats
PARSE=-use-menhir -yaccflag --explain # set to empty for ocamlyacc

all:
	([ -d out ] && echo "out/ exists") || (mkdir out && echo "out/ created")
	ocamlbuild $(LIBS) $(PARSE) $(LAM) $(STATS) -no-links main.native
	ln -f -s _build/main.native system-d

## bytecode version with debugging
##all:
##	ocamlbuild $(LIBS) $(PARSE) $(LAM) -no-links main.d.byte
##	ln -f -s _build/main.d.byte system-d

loc:
	wc -l lang.ml langUtils.ml zzz.ml                 \
    sub.ml wf.ml tcUtils.ml                         \
    cnf.ml anf.ml main.ml                           \
    utils.ml log.ml                                 \
    tcDref2.ml                                      \
    parseUtils.ml                                   \
    djsDesugar.ml                                   \
    settings.ml                                     \
    langLexer.mll langParser.mly                    \
    theory*.lisp prims/*                         

clean:
	rm -rf _build out system-d

