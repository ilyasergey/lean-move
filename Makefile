PROJECT = lean-move

zip:
	git archive --format=zip --prefix=$(PROJECT)/ -o $(PROJECT).zip HEAD
