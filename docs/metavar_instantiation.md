Meta Variable Instantiation
===========================

\newcommand {\posvar} {\mathrm{Pos}}
\newcommand {\negvar} {\mathrm{Neg}}
\newcommand {\freshvar} {\mathrm{Fresh}}
\newcommand {\appvar} {\mathrm{App}}

\newcommand {\MetaVar} {\mathrm{MetaVar}}
\newcommand {\EVar} {\mathrm{EVar}}
\newcommand {\SVar} {\mathrm{SVar}}

Notation:

*   Lower case $\phi$, $\psi$ for (object-level) meta-variables
*   Upper case $\Psi$, $\alpha$, $\beta$ for meta-level patterns/meta-patterns

Meta-criteria
:   A meta-criteria is a pair, $(\chi, \rho)$
    where, $\chi \in \EVar \union \SVar$,
       and $\rho \subset \{ \freshvar, \posvar, \negvar, \appvar \}$.

Meta-variable
:   A metavariable is a pair $(\phi, C)$,
    $\phi$ is drawn from a countable set $\MetaVar$, and $C$ is a finite set of meta-criteria with distinct $\chi$s.
    We call $\phi$ its name.

Well-formed meta-pattern
:   We call a meta-pattern *well-formed* if every meta-variable with the same name has the same meta-criteria.
    TODO Talk about $\mu$ binders.

**From here on, we assume that all meta-patterns are well-formed.**

Instantiable meta-pattern

:   We call a pattern $\Psi$ *instantiable*, if there is a substitution for all metavariables,
    that has a concrete co-domain, and meets the meta-criteria.
    We call the set of patterns that instantiate a meta-pattern its instantiations.

::: { .theorem }
Let $\Psi$ be a concrete pattern that satisfies $\rho\subset \{ \freshvar, \posvar, \negvar, \appvar \}$.

Then,

* `(monotonic)`: if $\rho'$ is a subset of $\rho$, then $\Psi$ also meets the meta-criteria of $\rho$.
* `(fresh-iff-pos-neg)`
    * if $\freshvar \in \rho$, $\Psi$ also meets the meta-criteria $\rho \union \{\posvar, \negvar\}$
    * if $\{\posvar, \negvar\} \subset \rho$, $\Psi$ also meets the meta-criteria $\rho \union \{\freshvar \}$
* `(app-implies-pos)`: if $\appvar \in \rho$, $\Psi$ also meets the meta-criteria $\rho \union \{\posvar\}$
* `(uninst-fresh-app)`: $\{\freshvar, \appvar\} \not\subset \rho$.
* `(uninst-neg-app)`:   $\{\freshvar, \negvar\} \not\subset \rho$.

In particular, the *maximal meta-criteria* that $\Psi$ meets must be one of the following:

* the empty set,
* $\{\posvar \}$
* $\{\negvar \}$,
* $\{\appvar, \posvar \}$,
* $\{\freshvar, \posvar, \negvar \}$.

All other combinations of meta-criteria are either not satisfiable or not maximal.
:::

::: { .theorem }
Let $\Psi$ be a meta-pattern.
Then if each metavariable has meta-criteria that are individually satisfiable,
$\Psi$ is instantiable by at least one pattern that does not meet a stronger
:::
::: { .proof }
For each metavaraible $(\phi, C)$ in $\Psi$,
instantiate that meta-variable with nested application of all variables with criteria is $\{\appvar, \posvar \}$. E.g. $(X (Y Z))$ where $X$, $Y$, $Z$ are the variables that have $\appvar$ in the meta-criteria.
If this list is empty, instantiate with $\bot$.
Lift to other pattern in the obvious way.
:::


::: { .theorem }
Let $\Psi$ be a meta-pattern.
Then we can compute the exact maximal meta-criteria for that meta-pattern.
That is we there is atleast one instantiation that satisfies the meta-criteria,
and at least one that does not satisfy each stronger meta-criteria
:::
::: { .proof }
Suppose $\Psi = \alpha[\beta/X]$.
Let $\rho_{X,\alpha}$ be the meta-criteria corresponding to $X$ in $\alpha$.
Let $\rho_{X,\beta}$ be the meta-criteria corresponding to $X$ in $\beta$.
Let $\rho_{X,\Psi}$ be the meta-criteria we are calculating for $\Psi$.

-   Suppose $\rho_{X,\alpha}$ is $\{ \freshvar, \posvar, \negvar \}$, then $\rho_{\Psi} = \{ \freshvar, \posvar, \negvar \}$, since there is nothing to substitute.
-   Suppose $\rho_{X,\beta} = \{\freshvar, \posvar, \negvar \}$, then $\rho_{\Psi} = \{\freshvar, \posvar, \negvar \}$, since $X$ has been substituted away, and is fresh in the plug.
-   Suppose $\rho_{X,\beta} = \{\appvar, \posvar\}$,
    -  Suppose $\rho_{X,\alpha}$ is $\{ \posvar, \appvar \}$  then $\rho_{\Psi} = \{ \posvar, \appvar \}$.
       $X$ is occurs exactly once, in an application context, in both $\phi$ and $\psi$,  so must be positive and in an application context in the result.
    -  Suppose $\rho_{X,\alpha}$ is $\{ \posvar \}$  then $\rho_{\Psi} = \{ \posvar \}$.
       $X$ is positive in every occurance, of both $\phi$ and $\psi$ so must be positive in the result.
       However, since there are instantiations of $\phi$ where $X$ is not in an application context, $X$ does not meet the application context criteria in the result.
    -  Suppose $\rho_{X,\alpha}$ is $\{ \negvar \}$  then $\rho_{\Psi} = \{ \negvar \}$. ...
-   Suppose $\rho_{X,\beta} = \{\posvar\}$,
    -  Suppose $\rho_{X,\alpha}$ is $\{ \posvar \}$  or $\{ \posvar, \appvar \}$ then $\rho_{\Psi} = \{ \posvar \}$.
       $X$ is positive in every occurance, of both $\phi$ and $\psi$ so must be positive in the result.
    -  Suppose $\rho_{X,\alpha}$ is $\{ \negvar \}$  then $\rho_{\Psi} = \{ \negvar \}$. ...
-   Suppose $\rho_{X,\beta} = \{\negvar\}$,
    -  Suppose   $\rho_{X,\alpha}$ is $\{ \posvar \}$  or $\{ \posvar, \appvar \}$ then $\rho_{\Psi} = \{ \negvar \}$. ...
    -  Suppose   $\rho_{X,\alpha}$ is $\{ \negvar \}$  then $\rho_{\Psi} = \{ \posvar \}$. ...
-   Otherwise, if either $\rho_{\alpha}$ or $\rho_{\alpha}$ is $\{\}$, then $\rho_{\Psi} = \{ \}$

Let $\rho_{Y,\Psi}$ be the meta-criteria we are calculating for $\Psi$.

-   TODO
:::
