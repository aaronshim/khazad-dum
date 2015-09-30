SRC = src/vcgen.scala

all: help
	-[ -e classes ] || mkdir classes
	scalac -d classes ${SRC}

help:
	@echo "This script compiles the file(s) ${SRC}"
	@echo "Compiled classes are stored in the classes/ directory"
	@echo ""
	@echo "To run the example parser on a file use the"
	@echo "following syntax:"
	@echo ""
	@echo "    scala -cp classes VCGen imp/count.imp"
	@echo ""

.PHONY: all help
