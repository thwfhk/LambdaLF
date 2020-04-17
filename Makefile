OBJS = syntax.cmo lexer.cmo parser.cmo core.cmo main.cmo

all: $(OBJS) f

include .depend

# Build an executable typechecker
f: $(OBJS) main.cmo 
	@echo Linking $@
	ocamlc -o $@ $(OBJS) 

# Compile an ML module interface
%.cmi : %.mli
	ocamlc -c $<

# Compile an ML module implementation
%.cmo : %.ml
	ocamlc -c $<

# Generate ML files from a parser definition file
parser.ml parser.mli: parser.mly
	@rm -f $@
	ocamlyacc $<

# Generate ML files from a lexer definition file
lexer.ml lexer.mli: lexer.mll
	@rm -f $@
	ocamllex $<

# Clean up the directory
clean::
	rm -rf lexer.ml parser.ml parser.mli *.cm[io] f

# Rebuild intermodule dependencies
depend:: lexer.ml parser.ml
	ocamldep *.mli *.ml > .depend