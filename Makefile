PROJECT  = lean-move
ARTEFACT = $(PROJECT)-artefact
ANONDIR  = /tmp/$(ARTEFACT)-anon

.PHONY: build eval eval-lean eval-rust artefact artefact-anon clean

# Build and kernel-check the whole development from scratch.
# Fetches the prebuilt mathlib cache first, then re-checks every proof.
build:
	lake exe cache get
	lake build

# One-command evaluation of the whole artefact: the Lean proofs AND the paper's
# Section 6 performance benchmark.
eval: eval-lean eval-rust

# Lean only: fetch the mathlib cache, kernel-recheck every proof, then print the
# axiom dependencies of the soundness theorems — expect only
# [propext, Classical.choice, Quot.sound] and, crucially, NO sorryAx.
eval-lean:
	lake exe cache get
	lake build
	lake env lean scripts/AxiomCheck.lean

# Rust only (paper Section 6): build the benchmark and corroborate the
# performance claim on the bundled sample (no dataset download).
eval-rust:
	cd benchmark && ./corroborate.sh

# Artefact archive for OOPSLA Artifact Evaluation. The AE is single-blind
# (reviewers see the authors), so this archive is NOT anonymised — it keeps real
# names, the Makefile, LICENSE, ARTIFACT.md, etc. Produces $(ARTEFACT).zip.
artefact:
	git archive --format=zip --prefix=$(ARTEFACT)/ -o $(ARTEFACT).zip HEAD

# Anonymised archive for the double-blind paper supplement: drops the Makefile
# and scrubs identifying strings from .lean/.md/.mvir files. Produces
# $(ARTEFACT)-anon.zip.
artefact-anon:
	rm -rf $(ANONDIR)
	git archive --prefix=$(ARTEFACT)-anon/ HEAD | tar -x -C /tmp
	rm -f $(ANONDIR)/Makefile
	find $(ANONDIR) \( -name '*.lean' -o -name '*.md' -o -name '*.mvir' \) -exec sed -i '' \
		-e 's/Copyright Ilya Sergey/Copyright (anonymised)/g' \
		-e 's/as discussed with Todd/as discussed/g' \
		-e 's#https://github.com/tnowacki/[^ )]*#<anonymised repository>#g' \
		-e 's#tnowacki/sui#<anonymised>/sui#g' {} +
	cd /tmp && zip -rq $(ARTEFACT)-anon.zip $(ARTEFACT)-anon
	mv /tmp/$(ARTEFACT)-anon.zip ./$(ARTEFACT)-anon.zip
	rm -rf $(ANONDIR)

clean:
	rm -f $(ARTEFACT).zip $(ARTEFACT)-anon.zip
