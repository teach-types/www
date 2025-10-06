module Lecture10 where

import Prelude

import Exp              -- STLC terms in spine form
import Term             -- Typed STLC terms
import Check            -- Type checker

import Lexer            -- Tokens and lexical analysis
import Parser           -- Parsing STLC terms
import Parser.Monad     -- General parsing tools

import NatSignature     -- Constants for natural numbers
import ChurchNumerals   -- Encoding numbers as lambda-terms

import Test.Check       -- Testing the type checker

-- Command-line program

import Prelude.IO
import stlc

-- Weakening

import Term.Weakening
import Term.Weakening.Properties
import Term.Weakening.Properties.Id

-- Substitution

import Term.Substitution
import Term.Substitution.Properties

-- Definitional equality

import Term.Equality

-- Normalization

import Term.Normalization.EtaLong
