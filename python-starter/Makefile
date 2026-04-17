all: pca_serve

default: all

pca_serve:
	install ./pca_serve.sh $@


clean:
	rm -f pca_serve lab3.zip

SRC_DIRS := ./src

FILES := \
	Makefile \
	requirements.txt \
	.gitignore \
	pca_serve.sh \
	$(shell find $(SRC_DIRS) -name '*.py')

handin: lab3.zip

lab3.zip: $(FILES)
	zip $@ $^

.PHONY: clean native handin
