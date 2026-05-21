# Sen's Impossibility of a Paretian Liberal — Lean 4 Formalisation

Formalisation of Amartya Sen's Impossibility of a Paretian Liberal (1970) in Lean 4 with Mathlib.

## Overview

This repository contains a formal proof of Sen's Theorem II — that no Social Decision Function can simultaneously satisfy Unrestricted Domain (U), the Pareto Principle (P), and Minimal Liberalism (L').

## Structure

- `SenParadoxInLean.lean` — main formalisation file containing:
  - Definitions: Preference Relation, Weak Order, Profile, CCR, SWF, SDF
  - Conditions: U, P, L, L'
  - Helper lemmas: cycle contradiction, shared element case, disjoint case
  - Main theorem: `SenImpossibility`

## Reference

Sen, A.K. (1970). The Impossibility of a Paretian Liberal. Journal of Political Economy, 78(1), 152–157.

## Setup

Requires Lean 4 and Mathlib. Run `lake update` then `lake exe cache get` before opening in VS Code.