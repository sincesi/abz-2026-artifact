module IdentityDisclosureVerification

open util/integer

-- ============================================================
-- SIGNATURES: Data Schemas
-- ============================================================

sig Name {}
sig ZipCode {}
sig DOB {}
sig Sex {}
sig DrugName {}
sig DrugCode {}
sig UnitPrice {}

-- Generalisation function g : DrugName -> DrugCode
one sig G {
  g: DrugName -> one DrugCode
}

-- Original dataset
sig D_orig {
  name:     one Name,
  zip:      one ZipCode,
  dob:      one DOB,
  sex:      one Sex,
  drugName: one DrugName,
  price:    one UnitPrice,
  age:      one Int
}

-- Released dataset
-- name is absent: deletion by schema design
sig D_rel {
  zip:      one ZipCode,
  dob:      one DOB,
  sex:      one Sex,
  drugCode: one DrugCode,
  price:    one UnitPrice,
  age:      one Int
}

-- External dataset: attacker's auxiliary information
sig D_ext {
  name:     one Name,
  zip:      one ZipCode,
  dob:      one DOB,
  sex:      one Sex,
  drugName: one DrugName,
  drugCode: one DrugCode,
  price:    one UnitPrice,
  age:      one Int
}

-- ============================================================
-- BASIC SANITY FACTS
-- ============================================================

fact GeneralisationTotal {
  all dn: DrugName | one dn.(G.g)
}

-- ============================================================
-- DE-IDENTIFICATION RELATION T
--
-- Three families:
--   1. Generalisation
--   2. Deletion
--   3. Noise addition
-- ============================================================

-- ------------------------------------------------------------
-- T_gen: Generalisation
--
-- r.drugCode = g(o.drugName)
-- All other shared attributes are preserved exactly.
-- ------------------------------------------------------------
pred DeIdentified_gen[o: D_orig, r: D_rel] {

  -- Apply generalisation: r.drugCode = g(o.drugName)
  o.drugName.(G.g) = r.drugCode

  -- Preserve all other shared attributes
  o.price = r.price
  o.zip   = r.zip
  o.dob   = r.dob
  o.sex   = r.sex
  o.age   = r.age
}

-- ------------------------------------------------------------
-- T_del: Deletion
--
-- name is absent from D_rel.
-- All attributes in the released schema are preserved exactly.
--
-- In this schema, deletion is realised by omitting name from D_rel.
-- Since D_rel contains drugCode rather than drugName, the released
-- drug attribute is represented through the same generalisation map g.
-- ------------------------------------------------------------
pred DeIdentified_del[o: D_orig, r: D_rel] {

  -- Preserve all attributes in A_rel
  -- name is not in D_rel, hence no constraint on name is needed.
  o.zip   = r.zip
  o.dob   = r.dob
  o.sex   = r.sex
  o.price = r.price
  o.age   = r.age

  -- Drug name is represented by its released code
  o.drugName.(G.g) = r.drugCode
}

-- ------------------------------------------------------------
-- T_noise: Noise Addition
--
-- r.age is within [o.age - n, o.age + n].
-- All other shared attributes are preserved exactly.
--
-- This is the original bounded-noise formulation.
-- Note: this allows zero noise, i.e. r.age = o.age.
-- ------------------------------------------------------------
pred DeIdentified_noise[o: D_orig, r: D_rel] {

  -- Preserve shared attributes
  o.zip   = r.zip
  o.dob   = r.dob
  o.sex   = r.sex
  o.price = r.price
  o.drugName.(G.g) = r.drugCode

  -- Apply bounded noise to age
  let n = 2 |
    gte[r.age, sub[o.age, n]] and
    lte[r.age, add[o.age, n]]
}

-- ------------------------------------------------------------
-- T_noise_nonzero: Non-zero Noise Addition
--
-- This auxiliary variant is useful when the intended experiment
-- requires exact matching to fail after perturbation.
-- It is not the minimal original noise relation, but a strengthened
-- version used to rule out r.age = o.age.
-- ------------------------------------------------------------
pred DeIdentified_noise_nonzero[o: D_orig, r: D_rel] {

  -- Preserve shared attributes
  o.zip   = r.zip
  o.dob   = r.dob
  o.sex   = r.sex
  o.price = r.price
  o.drugName.(G.g) = r.drugCode

  -- Apply non-zero bounded noise to age
  let n = 2 |
    gte[r.age, sub[o.age, n]] and
    lte[r.age, add[o.age, n]] and
    r.age != o.age
}

-- ============================================================
-- RE-IDENTIFICATION RELATION R
--
-- Two attacker models:
--   1. Exact matching
--   2. Approximate matching
-- ============================================================

-- ------------------------------------------------------------
-- R_exact: Exact Matching
--
-- All shared matching attributes coincide exactly.
-- ------------------------------------------------------------
pred ReIdentified_exact[r: D_rel, e: D_ext] {

  -- Exact equality on all matching attributes
  r.zip      = e.zip
  r.dob      = e.dob
  r.sex      = e.sex
  r.price    = e.price
  r.drugCode = e.drugCode
  r.age      = e.age
}

-- ------------------------------------------------------------
-- R_approx: Approximate Matching
--
-- All categorical attributes match exactly.
-- The numerical attribute age may differ within bound k.
-- ------------------------------------------------------------
pred ReIdentified_approx[r: D_rel, e: D_ext] {

  -- Exact match on categorical attributes
  r.zip      = e.zip
  r.dob      = e.dob
  r.sex      = e.sex
  r.price    = e.price
  r.drugCode = e.drugCode

  -- Approximate match on numeric attribute age
  -- abs(r.age - e.age) <= k
  let k = 2, diff = sub[r.age, e.age] |
    gte[diff, sub[0, k]] and
    lte[diff, k]
}

-- ============================================================
-- IDENTITY DISCLOSURE AS RELATIONAL REACHABILITY
--
-- A disclosure witness is a path:
--
--     D_orig --T--> D_rel --R--> D_ext
--
-- such that the original record and the external record refer
-- to the same direct identifier name.
-- ============================================================

pred IdentityDisclosure_gen_exact[o: D_orig, r: D_rel, e: D_ext] {
  DeIdentified_gen[o, r]
  ReIdentified_exact[r, e]
  o.name = e.name
}

pred IdentityDisclosure_del_exact[o: D_orig, r: D_rel, e: D_ext] {
  DeIdentified_del[o, r]
  ReIdentified_exact[r, e]
  o.name = e.name
}

pred IdentityDisclosure_noise_exact[o: D_orig, r: D_rel, e: D_ext] {
  DeIdentified_noise[o, r]
  ReIdentified_exact[r, e]
  o.name = e.name
}

pred IdentityDisclosure_noise_approx[o: D_orig, r: D_rel, e: D_ext] {
  DeIdentified_noise[o, r]
  ReIdentified_approx[r, e]
  o.name = e.name
}

pred IdentityDisclosure_noise_nonzero_exact[o: D_orig, r: D_rel, e: D_ext] {
  DeIdentified_noise_nonzero[o, r]
  ReIdentified_exact[r, e]
  o.name = e.name
}

pred IdentityDisclosure_noise_nonzero_approx[o: D_orig, r: D_rel, e: D_ext] {
  DeIdentified_noise_nonzero[o, r]
  ReIdentified_approx[r, e]
  o.name = e.name
}

-- ============================================================
-- GENERIC IDENTITY DISCLOSURE PREDICATE
--
-- This version corresponds to the paper-level definition:
--
--   exists r : D_rel .
--     DeIdentified[o,r] and ReIdentified[r,e] and o.name = e.name
--
-- Since Alloy predicates cannot be passed as first-class arguments
-- in the same way as functions in a programming language, the executable
-- runs below instantiate this generic idea separately for each T/R pair.
-- ============================================================

pred IdentityDisclosure_original_style[o: D_orig, e: D_ext] {
  some r: D_rel |
    DeIdentified_gen[o, r] and
    ReIdentified_exact[r, e] and
    o.name = e.name
}

-- ============================================================
-- VERIFICATION RUNS
-- Original ABZ-style cases
-- ============================================================

-- ------------------------------------------------------------
-- Case 1: Generalisation + Exact Matching
-- Expected: SAT
-- ------------------------------------------------------------
run case1_gen_exact {
  some o: D_orig, r: D_rel, e: D_ext |
    IdentityDisclosure_gen_exact[o, r, e]
} for 3 but 1 D_orig, 1 D_rel, 1 D_ext, 6 Int

-- ------------------------------------------------------------
-- Case 2: Deletion + Exact Matching
-- Expected: SAT
-- ------------------------------------------------------------
run case2_del_exact {
  some o: D_orig, r: D_rel, e: D_ext |
    IdentityDisclosure_del_exact[o, r, e]
} for 3 but 1 D_orig, 1 D_rel, 1 D_ext, 6 Int

-- ------------------------------------------------------------
-- Case 3: Noise + Approximate Matching
-- Expected: SAT
-- ------------------------------------------------------------
run case3_noise_approx {
  some o: D_orig, r: D_rel, e: D_ext |
    IdentityDisclosure_noise_approx[o, r, e]
} for 3 but 1 D_orig, 1 D_rel, 1 D_ext, 6 Int

-- ------------------------------------------------------------
-- Case 4: Noise + Exact Matching
--
-- Important:
-- With the original bounded-noise relation, this may be SAT,
-- because zero noise is allowed: r.age = o.age.
-- ------------------------------------------------------------
run case4_noise_exact_original {
  some o: D_orig, r: D_rel, e: D_ext |
    IdentityDisclosure_noise_exact[o, r, e]
} for 3 but 1 D_orig, 1 D_rel, 1 D_ext, 6 Int

-- ------------------------------------------------------------
-- Case 4': Non-zero Noise + Exact Matching
--
-- Expected: UNSAT under the strengthened non-zero noise relation.
-- This is the controlled version used when exact re-identification
-- should be blocked by perturbation.
-- ------------------------------------------------------------
run case4_noise_nonzero_exact {
  some o: D_orig, r: D_rel, e: D_ext |
    IdentityDisclosure_noise_nonzero_exact[o, r, e]
} for 3 but 1 D_orig, 1 D_rel, 1 D_ext, 6 Int

-- ============================================================
-- ASSERTIONS
-- ============================================================

-- ------------------------------------------------------------
-- This assertion is generally NOT valid for the original noise model,
-- because original bounded noise allows r.age = o.age.
-- It is included as a diagnostic check.
-- ------------------------------------------------------------
assert OriginalNoisePreventsExactReidentification {
  no o: D_orig, r: D_rel, e: D_ext |
    IdentityDisclosure_noise_exact[o, r, e]
}

check OriginalNoisePreventsExactReidentification
  for 3 but 1 D_orig, 1 D_rel, 1 D_ext, 6 Int

-- ------------------------------------------------------------
-- This assertion should hold for the strengthened non-zero noise model.
-- ------------------------------------------------------------
assert NonzeroNoisePreventsExactReidentification {
  no o: D_orig, r: D_rel, e: D_ext |
    IdentityDisclosure_noise_nonzero_exact[o, r, e]
}

check NonzeroNoisePreventsExactReidentification
  for 3 but 1 D_orig, 1 D_rel, 1 D_ext, 6 Int

-- ============================================================
-- WITNESS INSPECTION HELPERS
-- ============================================================

run ShowWitness_gen_exact {
  some o: D_orig, r: D_rel, e: D_ext |
    IdentityDisclosure_gen_exact[o, r, e]
} for 3 but 1 D_orig, 1 D_rel, 1 D_ext, 6 Int

run ShowWitness_del_exact {
  some o: D_orig, r: D_rel, e: D_ext |
    IdentityDisclosure_del_exact[o, r, e]
} for 3 but 1 D_orig, 1 D_rel, 1 D_ext, 6 Int

run ShowWitness_noise_approx {
  some o: D_orig, r: D_rel, e: D_ext |
    IdentityDisclosure_noise_approx[o, r, e]
} for 3 but 1 D_orig, 1 D_rel, 1 D_ext, 6 Int

run ShowWitness_noise_exact_original {
  some o: D_orig, r: D_rel, e: D_ext |
    IdentityDisclosure_noise_exact[o, r, e]
} for 3 but 1 D_orig, 1 D_rel, 1 D_ext, 6 Int

run ShowWitness_noise_nonzero_approx {
  some o: D_orig, r: D_rel, e: D_ext |
    IdentityDisclosure_noise_nonzero_approx[o, r, e]
} for 3 but 1 D_orig, 1 D_rel, 1 D_ext, 6 Int
