module Lecture8 where

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
