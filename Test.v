Require Extraction.

Require Import Euclid Wf_nat.

Extraction Inline gt_wf_rec lt_wf_rec induction_ltof2.
Recursive Extraction eucl_dev.
Extraction "Test.ml" eucl_dev.
