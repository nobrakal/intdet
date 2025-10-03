build:
	dune build

all: build

clean:
	dune clean
	find . -name "*.lia.cache" -type f -delete
	find . -name "*.nia.cache" -type f -delete
