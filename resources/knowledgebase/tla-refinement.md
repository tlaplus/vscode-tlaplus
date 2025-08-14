---
title: TLA+ Spec Refinement
description: Understanding and verifying refinement in TLA+ specifications.
---
## 📏 TLA+ Spec Refinement

### 🔍 What is Refinement?

**Refinement** means that a **lower-level (implementation) specification** correctly implements the behavior of a **higher-level (abstract) specification**. In TLA+, this allows you to write a simple spec describing *what* a system should do, and a more detailed one describing *how* it does it—and then prove they behave consistently. In short: **Implementation Spec** refines **High-Level Spec** if every behavior of the implementation is *allowed* by the high-level spec.
Refinement is semantic: it’s about the meaning of the specs (their behaviors), not about syntax. Specs don’t have to share variables or modules.

---

### ✅ How to Check Refinement with TLC

**General Process:**

1. Write the missing specification: either the abstract (high-level) or the concrete (implementation-level) specification, depending on which one already exists. Typically, one of the two is already defined and remains unchanged.
2. **Instantiate the abstract specification** in the concrete one using the `INSTANCE` statement.
3. **Define a refinement mapping** with the `WITH` clause, relating implementation variables to abstract variables, if needed.
4. **Verify refinement using TLC** by ensuring that the abstract specification is a `PROPERTY` of the concrete specification.

---

### 🧪 Example

Assume you have:

* A high-level spec in a module named `HighLevel`
* An implementation spec in a module named `Impl`

```tla
------------------- MODULE HighLevel -------------------
VARIABLE counter

Init == counter = 0
Next == counter' = counter + 1

Spec == Init /\ [][Next]_counter
========================================================
```

```tla
------------------- MODULE Impl -------------------
EXTENDS Naturals

VARIABLE x, y

Init == x = 0 /\ y = 0
Next == \/ x' = x + 1 /\ y' = y
        \/ x' = x /\ y' = y + 1

Spec == Init /\ [][Next]_<x, y>

----

High == INSTANCE HighLevel WITH counter <- x
Refinement == High!Spec
====================================================
```

In your TLC config file for `Impl`, set:

```cfg
SPECIFICATION Spec
PROPERTY Refinement
```

This checks: "Does my implementation spec (`Spec`) refine the abstract spec (`High!Spec`)?"

---

### 🧠 Advanced Notes

TLA+ refinement is **stuttering insensitive**. That means if your implementation does "extra steps" such as `x' = x /\ y' = y + 1` that don’t change the abstract state (the variable `counter` above), it's still a valid refinement—as long as the visible behavior aligns.

> 🧠 Think of it as: the abstract spec doesn’t care *how* the result was achieved, as long as the *resulting behavior* is the same.
