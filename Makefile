PROJECT  = lean-move
ARTEFACT = $(PROJECT)-artefact
STAGE    = /tmp/$(ARTEFACT)

.PHONY: build artefact zip clean

# Build and kernel-check the whole development from scratch.
# Fetches the prebuilt mathlib cache first, then re-checks every proof.
build:
	lake exe cache get
	lake build

# Artefact archive for OOPSLA Artifact Evaluation (and the paper supplement).
# Produces $(ARTEFACT).zip. The paper is under double-blind revision, so the
# tree is anonymised: the Makefile is dropped and identifying strings are
# scrubbed from .lean/.md/.mvir files.
artefact:
	rm -rf $(STAGE)
	git archive --prefix=$(ARTEFACT)/ HEAD | tar -x -C /tmp
	rm -f $(STAGE)/Makefile
	find $(STAGE) \( -name '*.lean' -o -name '*.md' -o -name '*.mvir' \) -exec sed -i '' \
		-e 's/Copyright Ilya Sergey/Copyright (anonymised)/g' \
		-e 's/as discussed with Todd/as discussed/g' \
		-e 's#https://github.com/tnowacki/[^ )]*#<anonymised repository>#g' \
		-e 's#tnowacki/sui#<anonymised>/sui#g' {} +
	cd /tmp && zip -rq $(ARTEFACT).zip $(ARTEFACT)
	mv /tmp/$(ARTEFACT).zip ./$(ARTEFACT).zip
	rm -rf $(STAGE)

# Plain (non-anonymised) source archive, e.g. for the post-acceptance Zenodo deposit.
zip:
	git archive --format=zip --prefix=$(PROJECT)/ -o $(PROJECT).zip HEAD

clean:
	rm -f $(PROJECT).zip $(ARTEFACT).zip
