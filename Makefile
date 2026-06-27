PROJECT = lean-move
ANON_DIR = /tmp/$(PROJECT)-anon

zip:
	git archive --format=zip --prefix=$(PROJECT)/ -o $(PROJECT).zip HEAD

zip-anon:
	rm -rf $(ANON_DIR)
	git archive --prefix=$(PROJECT)/ HEAD | tar -x -C /tmp
	mv /tmp/$(PROJECT) $(ANON_DIR)
	rm -f $(ANON_DIR)/Makefile
	find $(ANON_DIR) \( -name '*.lean' -o -name '*.md' -o -name '*.mvir' \) -exec sed -i '' \
		-e 's/Copyright Ilya Sergey/Copyright (anonymised)/g' \
		-e 's/as discussed with Todd/as discussed/g' \
		-e 's#https://github.com/tnowacki/[^ )]*#<anonymised repository>#g' \
		-e 's#tnowacki/sui#<anonymised>/sui#g' {} +
	cd /tmp && zip -rq $(PROJECT)-anon.zip $(PROJECT)-anon
	mv /tmp/$(PROJECT)-anon.zip ./$(PROJECT)-anon.zip
	rm -rf $(ANON_DIR)

clean:
	rm -f $(PROJECT).zip $(PROJECT)-anon.zip
