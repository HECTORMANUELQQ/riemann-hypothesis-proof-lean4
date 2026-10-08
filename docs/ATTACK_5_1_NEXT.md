# ATTACK 5.1 — siguiente mordida tipable (leftoverInterior)

**Fecha:** 2026-09-16 ~05:10 CT (UTC-6)  
**Objetivo:** vaciar / encoger `leftoverInterior \ U` (PROGRESO §5.1 / Status OPEN).  
**Política:** sin prueba falsa de RH · sin axiom RH · Lean = prueba.

> Destino Windows: `C:\Users\cuent\Desktop\trabajo\rh_g1_lean\ATTACK_5_1_NEXT.md`  
> (este archivo se generó en el box; si falta en manuel, copiar con CopyFromBox).

---

## 1. Hallazgos mathlib (cero-libre / nonvanishing)

Escaneo vía fuentes oficiales mathlib4 (`Mathlib/NumberTheory/LSeries/*`, `Harmonic/ZetaAsymp.lean`).  
**No hay región libre de ceros dentro de la franja crítica** ni nada que cubra `|t|≤1/2` con `Re s < 1`.

| Lema | Archivo | Región / qué cubre |
|---|---|---|
| `riemannZeta_ne_zero_of_one_lt_re` | `LSeries/Dirichlet.lean` | `Re s > 1` |
| `riemannZeta_ne_zero_of_one_le_re` | `LSeries/Nonvanishing.lean` | `Re s ≥ 1` (junk en s=1 ≠ 0) |
| `DirichletCharacter.LFunction_ne_zero_of_one_le_re` | `Nonvanishing.lean` | L(χ,s) ≠ 0 si `Re≥1` (salvo χ trivial y s=1) |
| `DirichletCharacter.LFunction_ne_zero_of_re_eq_one` | `Nonvanishing.lean` | `Re s = 1`, χ trivial ⇒ s≠1 |
| `riemannZeta_one_ne_zero` | `Harmonic/ZetaAsymp.lean` | junk `ζ(1) ≠ 0` |
| `riemannZeta_eventually_ne_zero_nhds_one` | `ZetaAsymp.lean` | `∀ᶠ s in 𝓝 1, ζ s ≠ 0` (**ya usado** en LeftoverNonvanishing) |
| `riemannZeta₁_ne_zero_of_near_one` | `ZetaAsymp.lean` | factor holomorfo cerca de 1 |
| `IsCompact.inter_riemannZetaZeros_finite` | `LSeries/ZetaZeros.lean` | finitos ceros en compacto (**ya usado**) |
| `isDiscrete_riemannZetaZeros` / `isClosed_riemannZetaZeros` | `ZetaZeros.lean` | discreción; no N=0 |
| `riemannZeta_neg_two_mul_nat_add_one` | `RiemannZeta.lean` | ceros triviales `ζ(-2(n+1))=0` |
| `riemannZeta_pos_of_one_lt` / `riemannZeta_re_pos_of_one_lt` / `riemannZeta_im_eq_zero_of_one_lt` | `Dirichlet.lean` (+ Positivity) | **reales** `x > 1`: ζ>0 (orden complejo) |
| `LSeries.positive` / `positive_of_differentiable_of_eqOn` | `LSeries/Positivity.lean` | positividad de L-series con coef ≥0; **no** da franja |
| `completedRiemannZeta₀_one_sub` / `completedRiemannZeta_one_sub` / `riemannZeta_one_sub` | `RiemannZeta.lean` | FE; puente de simetría |
| `riemannZeta_conj` | `ZetaAsymp.lean` | `ζ(conj s)=conj(ζ s)` **para todo s** (New Bot C1: **no duplicar**; ya está en mathlib) |
| `Gammaℝ_ne_zero_of_re_pos` (vía Gamma) | varios | factor Γℝ ≠0 si Re>0 — útil en la caja |

**Ausente en mathlib (relevante a 5.1):**
- Cualquier zero-free strip tipo `σ ≥ 1 − c/log(|t|+2)`.
- `ζ ≠ 0` en el intervalo real `(0,1)`.
- Dirichlet eta `η(s)=(1−2^{1−s})ζ(s)` y su no-anulación en `Re>0`.
- Cota inferior explícita de `|ξ|` / `|ζ|` en compactos de la franja.

Conclusión: mathlib **ya dio** todo lo que muerde el borde derecho y un entorno de 1; **no** muerde el interior `½ ≤ Re < 1`, `|Im| ≤ ½`.

---

## 2. Lean local — sorry / planes abiertos

Archivos revisados (uploads + copias box: `Status`, `Leftover*`, `FunEq`, `Nonvanishing`, `G5*`, `Split`, deliver `LeftoverNonvanishing`):

- **No hay `sorry` de prueba** de leftover / RH. Status declara explícitamente: sin axiom RH, sin sorry de RH.
- OPEN documentado (Status / PROGRESO §5.1 / prospecto 66):
  - `leftoverInterior \ U` vacío de ceros
  - G2 compacto `|y|<1/2` ξ≠0
  - cota numérica `|ξ|` en compacto
  - N=0 / RH
- FILLED útil ya empaquetado: cara derecha, nhds/bola en 1, compacto `leftoverRect\U` + finitos, `riemannXi_eq_zero_iff_zeta_leftoverRect`, FE `completedRiemannZeta₀_symmetric`, `stripO1Small_neg`.
- Comentarios de plan (no código): ataque = ZF cerca del eje real **o** cota `|ξ|` + máx/argumento en **ese** compacto; rosas/Pick fuera (`γ≥14`).

Nota: el prompt menciona FILLED adicionales (`GammaR≠0` en caja, min de `‖ξ‖` existe, `mem_leftoverInterior_of_stripO1Small`, iff completedRiemannZeta). En las copias locales del box esas piezas **no** aparecen aún como teoremas con esos nombres; si están solo en manuel, el átomo recomendado abajo asume el puente ξ↔ζ ya FILLED (`riemannXi_eq_zero_iff_zeta_leftoverRect`) y el corte métrico (`exists_compact_leftoverCore_cut`).

---

## 3. ¿Puede el mínimo de `‖ξ‖` forzar `min > 0`?

**No — honestamente no**, con lo que hay.

- Existencia de un mínimo de `‖ξ‖` en un compacto (continuidad + compacto) **no** implica que el mínimo sea positivo.
- `min = 0` ↔ existe cero de ξ en el compacto ↔ (por ξ↔ζ en leftoverRect, s≠1) existe cero de ζ.
- Forzar `min > 0` **es** vaciar el núcleo: equivale al OPEN 5.1 en ese compacto. No hay lema local ni mathlib que lo regale.
- El majorante M(σ) solo vive en `Re>1`; no baja a leftoverInterior.

Por tanto: el camino `|ξ|` es correcto como **certificado** (acota m>0 en el compacto + AP/máximo), pero **no** es un tip automático desde el mínimo existencial.

---

## 4. Teorema recomendado (UNA mordida)

### Nombre
`leftoverCore_zeta_ne_zero_of_xi_min_pos`

### Enunciado Lean (borrador tipable)

```lean
/-- Mordida 5.1 (ruta |ξ|): si ‖ξ‖ está acotada inferiormente por m>0
en el núcleo compacto leftoverRect \ ball(1,ε), entonces no hay ceros de ζ
en leftoverInterior fuera de esa bola. Reduce el OPEN a producir m>0
(certificado), sin declarar RH. -/
theorem leftoverCore_zeta_ne_zero_of_xi_min_pos
    {ε m : ℝ} (hε : 0 < ε) (hm : 0 < m)
    (hmin : ∀ s ∈ leftoverRect \ Metric.ball (1 : ℂ) ε,
      ‖riemannXi s‖ ≥ m) :
    ∀ s ∈ leftoverInterior \ Metric.ball (1 : ℂ) ε,
      riemannZeta s ≠ 0 := by
  intro s hs
  have hsR : s ∈ leftoverRect := hs.1.1
  have h1 : s ≠ 1 := ne_one_of_mem_leftoverInterior hs.1
  -- s ∈ leftoverRect \ ball 1 ε
  have hsCore : s ∈ leftoverRect \ Metric.ball (1 : ℂ) ε := ⟨hsR, hs.2⟩
  have hξ : riemannXi s ≠ 0 := by
    have := hmin s hsCore
    exact norm_pos_iff.mp (lt_of_lt_of_le hm this)
  exact (riemannXi_eq_zero_iff_zeta_leftoverRect hsR h1).not.mp hξ
```

### Por qué esta y no otra
- **Tipable ahora** con mathlib + lemas FILLED del proyecto (`exists_compact_leftoverCore_cut` / bola, `riemannXi_eq_zero_iff_zeta_leftoverRect`, defs leftoverInterior).
- **Muerde 5.1 de verdad**: convierte el OPEN en “exhibir `m>0` en el compacto” — exactamente la receta PROGRESO §5.1 (cota `|ξ|` + principio).
- No inventa RH: la conclusión es condicional a `hmin`.
- No duplica C1 (`riemannZeta_conj` ya en mathlib) ni A1/A2/B.

### Tipable ahora?
**Sí** (el teorema condicional arriba).

### Un blocker
**Producir `m > 0`** (cota inferior estricta de `‖ξ‖` en `leftoverRect \ ball(1,ε)`). Eso **no** tipa con mathlib actual; exige certificado analítico nuevo (o trabajo clásico formalizado). Mientras `m>0` no esté, 5.1 sigue OPEN.

---

## 5. Alternativa clásica (encoge el eje; no tipable hoy)

Si se prefiere **encoger** el locus sin esperar `|ξ|`:

**Clásico (citeable, ausente en mathlib):**  
`∀ σ ∈ (0,1), riemannZeta σ ≠ 0`  
(prueba estándar vía η(s)=(1−2^{1−s})ζ(s), serie alternada η(σ)>0, factor ≠0).

Consecuencia local:
```lean
theorem leftoverInterior_real_zeta_ne_zero {s : ℂ}
    (hs : s ∈ leftoverInterior) (him : s.im = 0) :
    riemannZeta s ≠ 0
```
Eso vacía el segmento real `[½,1) ∩ leftoverInterior`, pero **deja** el resto `Im≠0`.  
**No tipable ahora** sin construir eta / FE-positivity. **Axiom solo si inevitable** — preferir lemas (eta + identidad). No recomendado como siguiente tip; sí como ruta clásica paralela.

---

## 6. Sketch de prueba / plan inmediato

1. **Tipar hoy** `leftoverCore_zeta_ne_zero_of_xi_min_pos` en `RhG1Lean/LeftoverCore.lean` (o archivo nuevo `LeftoverXiMin.lean`).
2. Registrar en `Status.lean` FILLED el condicional; OPEN afilado a:  
   `∃ ε m > 0, ∀ s ∈ leftoverRect \ ball 1 ε, ‖riemannXi s‖ ≥ m`.
3. Ataque a `m>0` (fuera de tip automático):
   - holomorfía ξ en el núcleo (ya `differentiableAt_riemannXi_leftoverRect`);
   - cota en frontera del núcleo + máximo módulo / argumento;
   - **no** plots; certificado Lean o lema clásico formalizable.
4. No listar γ; no Pick/rosas; no majorante Re>1 como si mordiera el interior.

---

## 7. Citas

- mathlib:  
  `Mathlib/NumberTheory/LSeries/Nonvanishing.lean`  
  `Mathlib/NumberTheory/LSeries/ZetaZeros.lean`  
  `Mathlib/NumberTheory/LSeries/Dirichlet.lean`  
  `Mathlib/NumberTheory/LSeries/Positivity.lean`  
  `Mathlib/NumberTheory/LSeries/RiemannZeta.lean`  
  `Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean` (`riemannZeta_conj`, nhds_one)
- local:  
  `RhG1Lean/LeftoverNonvanishing.lean`  
  `RhG1Lean/LeftoverCore.lean`  
  `RhG1Lean/LeftoverCompact.lean`  
  `RhG1Lean/FunEq.lean`  
  `RhG1Lean/Status.lean`  
  `PROGRESO_DETALLADO.md` §5.1  
  prospecto `66_gap51_leftover_nhds_cut.md`

---

## 8. Resumen ejecutivo

| Ítem | Valor |
|---|---|
| **Teorema recomendado** | `leftoverCore_zeta_ne_zero_of_xi_min_pos` |
| **Tipable ahora** | **Sí** (condicional a `m>0`) |
| **Un blocker** | Exhibir `m>0` = cota inferior de `‖ξ‖` en el núcleo compacto (mathlib no lo da; ≈ vaciar 5.1) |
| **RH** | Sigue OPEN |

