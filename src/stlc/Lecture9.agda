-- DAT 350 / DIT 235  Types for programs and proofs 2026
--
-- Lecture 9: Reduction, Confluence, and Standardization
-- =====================================================

-- Small-step reduction for STLC

import Term.Reduction

-- Substitution: definition, composition

import Term.Substitution

-- Properties of substitution, including associativity (category law)

import Term.Substitution.Properties

-- Reflexive transitive closure, abstract confluence

import Prelude.Reduction

-- Closure properties of reduction: e.g. under substitution

import Term.Reduction.Properties

-- Parallel reduction proving confluence

import Term.Reduction.Parallel

-- Standard reduction (weak head steps first)

import Term.Reduction.Standard
