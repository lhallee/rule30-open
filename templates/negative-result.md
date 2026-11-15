---
title: <What failed and why, in one line, as the catalog will show it>
category: <an id from categories.yaml>
problems: [1]
status: negative
kind: dead-end
evidence: [computations/<module>.py]
---

# <What failed and why, in one line, as the catalog will show it>

<The question the approach asked, and the route it served. Link the entries it builds on.>

## What was done

<The search, test, or argument, with its range and, for a search that found nothing, the controls that show what it
could have found.>

## Outcome

<The result with its numbers: the counterexample for `refuted`, the step where it stops for `dead-end`, or the reason a
whole class of approaches fails for `barrier`.>

## What it means

<What the next person should not retry, and what would get past the stopping point. If the code is not in this
repository, say so here.>

## Reproduce

```bash
python -m computations.<module> <arguments>
```
