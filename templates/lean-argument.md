---
title: <The claim in one line, as the catalog will show it>
category: <an id from categories.yaml whose category has a lean directory>
problems: [1]
status: proved
lean: Rule30Open.<Directory>.<Name>
headline: [<main_theorem>, <center_form>]
kit: new
kit_modules: [<KitModule>]
evidence: [computations/<module>.py]
---

# <The claim in one line, as the catalog will show it>

<The result in a few sentences of mathematics, for a reader who will not open the Lean file.>

## Statement

- `<main_theorem>`: <the theorem in mathematical notation, for every starting row where the argument allows>.
- `<center_form>`: <the same statement for `Rule30Prize.center`, through `evolve_single_center`>.

## Argument

<The proof a reader can follow without Lean.>

## In Lean

<Where each step of the argument lives in the module: the definitions, the lemmas, and the kernel checks.>

## Relation to the kit

<What the kit has on this question, and how this module relates to it, matching the `kit` value.>

## Reproduce

<For a module whose data a computation prints: the command that prints it, as
`python -m computations.<module> --lean <Name> > Rule30Open/<Directory>/<Name>.lean`. Delete this section otherwise.>
