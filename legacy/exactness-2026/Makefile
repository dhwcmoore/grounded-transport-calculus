COQC ?= coqc
OCAMLC ?= ocamlc

.PHONY: check check-versions coq ocaml interface clean

check: check-versions coq ocaml interface

check-versions:
	@$(COQC) --version | grep -q "version 8.18.0" || \
	  (echo "Coq 8.18.0 required" >&2; exit 1)
	@test "$$($(OCAMLC) -version)" = "4.14.1" || \
	  (echo "OCaml 4.14.1 required" >&2; exit 1)

coq:
	$(COQC) Admissibility.v
	$(COQC) -Q . Exactness GroundedSeam.v
	$(COQC) -Q . Exactness SeamExtraction.v

ocaml:
	$(OCAMLC) -o examples admissibility.ml examples.ml
	./examples > examples_output.current.txt
	cmp examples_output.txt examples_output.current.txt
	$(OCAMLC) -o jurisdiction admissibility.ml jurisdiction.ml
	./jurisdiction > jurisdiction_output.current.txt
	cmp jurisdiction_output.txt jurisdiction_output.current.txt

interface: coq
	$(OCAMLC) -c seam_checks.mli
	$(OCAMLC) -c seam_checks.ml
	$(OCAMLC) -c certified_temporal_seam.mli
	$(OCAMLC) -c certified_temporal_seam.ml
	$(OCAMLC) -o interface_ok seam_checks.cmo certified_temporal_seam.cmo interface_ok.ml
	./interface_ok > interface_ok.current.txt
	grep -q "non-commuting evolution rejected at element 0" interface_ok.current.txt
	grep -q "grounded candidate certified" interface_ok.current.txt
	grep -q "rejected at request 1" interface_ok.current.txt
	@if $(OCAMLC) -c interface_direct_forge.ml > direct_forge.log 2>&1; then \
	  echo "direct construction unexpectedly compiled" >&2; exit 1; \
	else echo "direct construction rejected"; fi
	@if $(OCAMLC) -c interface_stage_mismatch.ml > stage_mismatch.log 2>&1; then \
	  echo "stage mismatch unexpectedly compiled" >&2; exit 1; \
	else echo "stage mismatch rejected"; fi
	$(OCAMLC) -o interface_unsafe_cast seam_checks.cmo certified_temporal_seam.cmo interface_unsafe_cast.ml
	./interface_unsafe_cast | grep -q "unsafe cast compiled"

clean:
	rm -f *.aux *.cmi *.cmo *.cmx *.o *.vo *.vos *.vok *.glob \
	  examples jurisdiction interface_ok interface_unsafe_cast \
	  examples_output.current.txt jurisdiction_output.current.txt interface_ok.current.txt \
	  direct_forge.log stage_mismatch.log seam_checks.ml seam_checks.mli .*.aux .lia.cache
