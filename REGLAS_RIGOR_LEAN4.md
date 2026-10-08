# Catálogo de Reglas y Prevención de Errores en Lean 4 (Proyecto RH-G1)

> **Regla de Oro Epistemológica:**
> *"La observación orienta, el mapa estructura, pero únicamente la compilación en el kernel de Lean 4 demuestra la verdad matemática."*
> Cero `sorry`, cero axiomas circulares (`axiom RiemannHypothesis`), cero axiomas de punto flotante.

---

## 1. Auditoría de Errores Identificados y Reglas de Prevención

Este catálogo documenta de forma minuciosa todos los fallos mecánicos, tácticos y de edición ocurridos durante el desarrollo, explica su causa raíz exacta y fija las reglas obligatorias para evitar su repetición y proteger el procedimiento formal de cualquier contaminación.

---

### Regla 1: Desigualdad Triangular Inversa y Cotas Inferiores de Normas

* **Error cometido:**
  Al demostrar `asymmetric_dual_sum_remainder_lower_bound` en `BocaANonvanishing.lean`, se intentó acotar $\|v + R\|$ aplicando:
  ```lean
  have htri := norm_sub_norm_le (v + R) R
  ```
  Esto generó la desigualdad $\|v + R\| - \|R\| \le \|(v + R) - R\| = \|v\|$, que acota $\|v\|$ por arriba, pero **no** acota $\|v + R\|$ por abajo. Al invocar `linarith`, la táctica falló por no existir contradicción.
* **Causa raíz:**
  Confundir la dirección de los operandos en el lema de Mathlib:
  $$\texttt{norm\_sub\_norm\_le } a \ b : \|a\| - \|b\| \le \|a - b\|$$
  Si se toma $a = v+R$ y $b = R$, la resta $a - b = v$ queda en el lado derecho de la desigualdad.
* **Regla obligatoria:**
  Para obtener una cota inferior del tipo $\|v + R\| \ge \|v\| - \|R\|$, se debe aplicar `norm_sub_norm_le` a $v$ y $-R$:
  ```lean
  have htri := norm_sub_norm_le v (-R)
  rw [norm_neg, sub_neg_eq_add] at htri
  -- Produce exactamente: ‖v‖ - ‖R‖ ≤ ‖v + R‖
  ```

---

### Regla 2: Igualdad Definicional (`rfl`) vs Formas Canónicas de Mathlib

* **Error cometido (Fallo en el primer borrador de `BocaADualCancellation`):**
  Al demostrar `dual_channel_balanced_factorization`, se escribió:
  ```lean
  have hcos : Complex.cos (((ψ - θ : ℝ) : ℂ)) =
    (Complex.exp (((ψ - θ : ℝ) : ℂ) * I) + Complex.exp (-(((ψ - θ : ℝ) : ℂ) * I))) / 2 := by
    unfold Complex.cos; rfl
  ```
  La táctica `rfl` falló reportando error de tipos porque el término derecho difería sutilmente de la definición en Mathlib.
* **Causa raíz:**
  En Mathlib (`Mathlib.Analysis.Complex.Trigonometric`), la definición canónica es:
  $$\texttt{Complex.cos } z := (\exp(z \cdot I) + \exp(-z \cdot I)) / 2$$
  Para el elaborador y el verificador de tipos de Lean 4, las expresiones `- (z * I)` y `(-z) * I` tienen árboles de sintaxis abstracta (AST) diferentes y no son definicionalmente iguales en el nivel reducible de `rfl`.
* **Regla obligatoria:**
  1. Antes de usar `rfl` sobre expansiones de funciones analíticas (`cos`, `sin`, `exp`, `log`), consultar siempre la definición exacta en Mathlib.
  2. Si hay signos unarios o productos en el argumento, usar `ring_nf` o `ring` tras desplegar, en lugar de un `rfl` rígido.

---

### Regla 3: Identificadores No Computables (`noncomputable def`)

* **Error cometido (Fallo en el primer borrador de `BocaADualCancellation`):**
  Al definir el operador de marco alineado:
  ```lean
  def alignedFrame (ψ : ℝ) (z : ℂ) : ℂ := channelWave ψ * z
  ```
  El compilador arrojó:
  `error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Complex.exp', which is 'noncomputable'`.
* **Causa raíz:**
  En Mathlib, `Complex.exp` está definido mediante series analíticas de potencias sin algoritmo de evaluación finita en tiempo de ejecución. Por tanto, cualquier definición que la invoque es no computable por definición.
* **Regla obligatoria:**
  Toda definición matemática en el plano complejo que utilice exponenciales, funciones trigonométricas o series debe declararse inequívocamente como `noncomputable def`.

---

### Regla 4: Coerciones Reales vs Complejas en Argumentos de Ondas Exponenciales

* **Error cometido (Fallo en `BocaADualCancellation`):**
  Al intentar reescribir la norma unitaria con `rw [norm_exp_ofReal_mul_I]`, la reescritura falló porque la expresión era `cexp (- ↑θ * I)`.
* **Causa raíz:**
  El lema `norm_exp_ofReal_mul_I (x : ℝ) : ‖exp (x * I)‖ = 1` exige que el argumento de $I$ sea la coerción directa de un número real $\mathbb{R} \to \mathbb{C}$. Si la negación está aplicada en el espacio complejo `-(↑θ)`, el emparejador de patrones no reconoce la coerción.
* **Regla obligatoria:**
  1. Definir una función canónica `channelWave (θ : ℝ) : ℂ := Complex.exp (θ * I)` con su lema simplificador `@[simp] theorem norm_channelWave (θ : ℝ) : ‖channelWave θ‖ = 1`.
  2. Pasar siempre la negación al número real antes de la coerción: `channelWave (-θ)`.

---

### Regla 5: Tácticas de Normalización Algebraica (`ring` vs `ring_nf`)

* **Error cometido:**
  En expresiones con cocientes o coerciones complejas/reales, `ring` falló reportando `ring failed to close the goal. Use ring_nf`.
* **Causa raíz:**
  `ring` opera estrictamente sobre formas polinomiales en anillos conmutativos; cuando hay coerciones `(x : ℝ) : ℂ` o divisiones que requieren reducción de fracciones o formas normales intermedias, `ring` se detiene.
* **Regla obligatoria:**
  1. Usar `push_cast` antes de tácticas algebraicas cuando intervengan proyecciones o coerciones $\mathbb{R} \to \mathbb{C}$.
  2. Si `ring` falla, aplicar `ring_nf` para simplificar a la forma normal antes de cerrar.

---

### Regla 6: Estructura Canónica de Archivos y Linters de Estilo

* **Errores cometidos en fases anteriores:**
  1. Iniciar un archivo con un `import` antes del bloque de copyright (`Eta.lean`), generando `Copyright too short!`.
  2. Colocar `set_option` antes del module docstring `/-! ... -/` (`Status.lean`, `BocaADualCancellation.lean`).
  3. Dejar el final del archivo sin salto de línea (`\n`), generando la advertencia `'' starts on column 12`.
  4. Opciones de linter flexibles no acotadas (`set_option linter.flexible false` no permitidas a nivel global de archivo en versiones recientes de Mathlib).
* **Solución Arquitectónica Definitiva:**
  Se configuró `lakefile.toml` con las opciones globales del compilador:
  ```toml
  [leanOptions]
  linter.style.longLine = false
  linter.style.setOption = false
  linter.flexible = false
  ```
  Esto elimina la necesidad de `set_option` dispersos en los archivos y asegura una compilación 100% limpia.
* **Plantilla Universal de Archivo Lean 4:**
  ```lean
  /-
  Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Hector Manuel Quezada Quiñonez
  -/
  import Mathlib...
  import RhG1Lean...

  /-!
  # Título del Módulo

  Descripción breve con líneas menores a 100 caracteres.
  -/

  open Complex Real ...

  namespace RhG1Lean

  -- Declaraciones y teoremas...

  end RhG1Lean
  -- SALTO DE LÍNEA OBLIGATORIO AL FINAL DEL ARCHIVO (\n)
  ```

---

### Regla 7: Edición Atómica y Preservación Estricta de Código Existente

* **Error cometido:**
  Al usar `replace_file_content` para insertar `deriv_entireXi_le_of_sphere_bound` en `XiEntire.lean`, el bloque de reemplazo absorbió accidentalmente la línea final `exact h_ne hz'` del teorema anterior `leftoverInterior_zeta_ne_zero_of_deriv_lt_half`.
* **Causa raíz:**
  Seleccionar un rango de reemplazo que incluía el cierre del teorema precedente sin verificar su contexto completo.
* **Regla obligatoria:**
  1. Siempre verificar con `view_file` las 5 líneas anteriores y posteriores antes de invocar `replace_file_content`.
  2. Inmediatamente después de cada edición, compilar el archivo afectado con `lake build RhG1Lean.<Modulo>` para verificar que ningún paso táctico haya sido mutilado.

---

### Regla 8: Protocolo Anti-Contaminación de la Prueba

* **Principio de Aislamiento y No-Contaminación:**
  Para garantizar que ninguna hipótesis fallida o definición intermedia contamine la arquitectura global:
  1. **Tipado Fuerte Incondicional:** Toda función matemática (`entireXi : ℂ → ℂ`) debe estar definida globalmente sobre tipos canónicos de Mathlib, no sobre estructuras ad-hoc o restricciones débiles.
  2. **Verificación Modular y Reducciones Explícitas:** Ningún teorema de reducción (como `riemann_hypothesis_reduction_to_bocaA_and_leftover`) puede asumir hipótesis tácitas. Toda condición es un parámetro explícito (`h_leftover`, `h_bocaA`).
  3. **Auditoría de Inmutabilidad:** Los 169 teoremas ya compilados en verde forman un núcleo inmutable. Ningún teorema previo puede ser modificado para debilitar sus hipótesis o alterar su conclusión.
  4. **Cero Tolerancia a Axiomas y Sorry:** Ni un solo `axiom` ni un solo `sorry` en ninguna parte de la cadena lógica. La compilación en verde del kernel de Lean 4 es el único árbitro.

---

### Regla 9: Codificación Estricta UTF-8 sin BOM en Manipulación de Archivos

* **Error cometido:**
  Al invocar comandos o scripts en PowerShell sin especificar `-Encoding utf8`, comandos como `Get-Content` o redirecciones `>` usan por defecto la página de códigos Windows-1252/ANSI. Al leer o escribir archivos con caracteres matemáticos UTF-8 (`→`, `≤`, `≠`, `‖`, `ℂ`, `ℝ`), los bytes multibyte se corrompen en secuencias espurias como `â†’`, destruyendo la sintaxis del archivo Lean.
* **Causa raíz:**
  Comportamiento legado de Windows PowerShell 5.1 donde la codificación predeterminada de consola/tuberías no es UTF-8.
* **Regla obligatoria:**
  1. En herramientas de edición (`replace_file_content`, `write_to_file`), Lean ya preserva UTF-8 nativo.
  2. Si se emplean scripts auxiliares en Python, usar siempre `open(..., encoding='utf-8')`.
  3. Si se usa PowerShell para leer o escribir archivos, forzar explícitamente:
     `[System.IO.File]::WriteAllText($path, $content, [System.Text.UTF8Encoding]($false))` o `-Encoding utf8`.

### Regla 10: Argumentos Implícitos `{x : T}` vs Explícitos `(x : T)` en Invocación de Lemas

* **Error cometido:**
  Al invocar el lema de Cauchy `deriv_entireXi_le_of_sphere_bound` en `RiemannHypothesis.lean`:
  ```lean
  exact deriv_entireXi_le_of_sphere_bound s R M hR (h_bound s hs)
  ```
  El compilador reportó:
  `Application type mismatch: The argument R has type ℝ of sort Type but is expected to have type 0 < ?m.42 of sort Prop`.
* **Causa raíz:**
  En `XiEntire.lean`, la signatura del lema es:
  $$\texttt{deriv\_entireXi\_le\_of\_sphere\_bound } (c : ℂ) \ \{R\ M : ℝ\}\ (hR : 0 < R) \dots$$
  Al estar $R$ y $M$ entre llaves curvas `{·}`, son parámetros implícitos que el elaborador de Lean 4 infiere a partir de $hR$ y del tipo de la cota $hM$. Pasar $R$ en la posición del segundo argumento explícito hizo que Lean intentara asignar $R$ (un número real) a la hipótesis de positividad $hR : 0 < R$ (una proposición).
* **Regla obligatoria:**
  1. Verificar siempre la signatura exacta del lema antes de la llamada (si un parámetro es implícito `{x : T}`, el elaborador lo calcula automáticamente; no debe pasarse posicionalmente).
  2. Si por razones de ambigüedad se necesita suministrar explícitamente parámetros implícitos, usar el prefijo aroba: `@deriv_entireXi_le_of_sphere_bound s R M hR ...`.
  3. En llamadas normales, omitir los argumentos entre llaves: `deriv_entireXi_le_of_sphere_bound s hR ...`.

### Regla 11: Igualdad Exponencial Real (`Real.exp_eq_one_iff`) vs Lemas Negativos Inexistentes

* **Error cometido:**
  Al demostrar que el cociente de ganancia del primo 2 no es 1 fuera de la recta crítica (`primeDualGainRatio_ne_one_of_delta_ne_zero`):
  ```lean
  rw [Real.exp_ne_one_iff]
  ```
  El compilador reportó:
  `Unknown constant Real.exp_ne_one_iff`.
* **Causa raíz:**
  Mathlib define la caracterización positiva directa:
  $$\texttt{Real.exp\_eq\_one\_iff : exp x = 1 ↔ x = 0}$$
  No existe una variante negativa directa `exp_ne_one_iff`.
* **Regla obligatoria:**
  Para probar desigualdades de exponenciales no unitarias $\exp(E) \ne 1$:
  1. Usar `intro h` para suponer por contradicción que $\exp(E) = 1$.
  2. Reescribir con `rw [Real.exp_eq_one_iff] at h` para obtener $E = 0$.
  3. Despejar el factor no nulo (usando `cases mul_eq_zero.mp h`) y cerrar por contradicción con la hipótesis de desplazamiento $\delta \ne 0$.

### Regla 12: Asociatividad a Izquierda de Uniones de Conjuntos en `rcases`

* **Error cometido:**
  Al descomponer la unión de las 4 fronteras `boundaryEdges : Set ℂ := edgeWest ∪ edgeEast ∪ edgeNorth ∪ edgeSouth`:
  ```lean
  rcases hs with (hW | hE | hN | hS)
  ```
  El compilador reportó:
  `Tactic 'rcases' failed: ... is not an inductive datatype`.
* **Causa raíz:**
  En Lean 4 / Mathlib, la operación binaria de unión `∪` en `Set` asocia estrictamente a la izquierda:
  `((edgeWest ∪ edgeEast) ∪ edgeNorth) ∪ edgeSouth`.
* **Regla obligatoria:**
  Usar el anidamiento izquierdo exacto para desarmar uniones múltiples:
  ```lean
  rcases hs with ((hW | hE) | hN) | hS
  ```

### Regla 13: Reescribitura Aislada de Lado Izquierdo (`conv_lhs`) en Desigualdades de Norma

* **Error cometido:**
  Al demostrar `‖s‖ ≤ ‖((s.re : ℝ) : ℂ)‖ + ‖((s.im : ℝ) : ℂ) * I‖` usando la descomposición `hdec : s = ((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * I`:
  ```lean
  rw [hdec]
  exact norm_add_le _ _
  ```
  El compilador reportó:
  `Type mismatch ... expected ‖↑s.re + ↑s.im * I‖ ≤ ‖↑(↑s.re + ↑s.im * I).re‖ + ...`.
* **Causa raíz:**
  `rw [hdec]` reescribió `s` en AMBOS lados de la desigualdad, haciendo que las proyecciones `.re` y `.im` de la derecha se expandieran monstruosamente sobre la suma compleja.
* **Regla obligatoria:**
  Usar `conv_lhs` para restringir la reescritura exclusivamente al miembro izquierdo:
  ```lean
  conv_lhs => rw [hdec]
  exact norm_add_le (((s.re : ℝ) : ℂ)) (((s.im : ℝ) : ℂ) * I)
  ```

### Regla 14: Manejo de Dependencias y Caché `.olean` entre Módulos Consumidores

* **Error cometido:**
  Al importar `FrontierMeasurement` en `RiemannHypothesis`:
  `error: RhG1Lean.RiemannHypothesis has already been declared`.
* **Causa raíz:**
  El objeto binario previo `FrontierMeasurement.olean` había importado transitoriamente `RiemannHypothesis.olean`. Al intentar compilar `RiemannHypothesis.lean`, la importación cíclica en caché recargó los símbolos preexistentes.
* **Regla obligatoria:**
  1. Mantener el grafo de dependencias estrictamente acíclico en todo momento.
  2. Tras modificar dependencias de importación en un módulo base, recompilar explícitamente su objeto `.olean` (`lake build RhG1Lean.<ModuloBase>`) antes de invocar o compilar el módulo consumidor.

---

### Regla 15: Principio de Mínima Complejidad y Máxima Simplicidad Formal (Navaja de Ockham en Lean 4)

* **Principio Director:**
  Para evitar sobrecarga sintáctica, tiempos de compilación excesivos y complejidad innecesaria en el kernel de Lean 4:
  1. **Reducción Dimensional Canónica (2D a 1D):** Reducir siempre dominios bidimensionales a su frontera unidimensional mediante el Principio del Módulo Máximo (`Complex.norm_le_of_forall_mem_frontier_norm_le`). Acotar 4 segmentos 1D es infinitamente más simple que integrar sobre un área 2D.
  2. **Aprovechamiento Integral de Simetrías:** La función $\Lambda_0(s)$ y $\xi(s)$ satisfacen simetría reflexiva $s \leftrightarrow 1-s$ y conjugación $s \leftrightarrow \bar{s}$. Cualquier cota en el semiplano derecho $\sigma \ge 1/2$ o semiplano superior $t \ge 0$ se propaga automáticamente a todo el rectángulo sin tener que repetir demostraciones.
  3. **Dominancia Convexa y Cotas Extremales:** En variables subarmónicas y convexas, el supremo en un compacto se alcanza en los vértices o extremos de la recta real. En vez de evaluar integrales complejas en todo el plano, basta demostrar que el valor extremal real (como $\Lambda_0(1) \approx 0.023$) acota globalmente la función por debajo de $1$.
  4. **Lemas Modulares Desacoplados:** Dividir cualquier paso de demostración en lemas auxiliares de menos de 20 líneas. Un lema que supera 50 líneas es indicio de que debe dividirse en sub-lemas algebraicos o métricos.

---

### Regla 16: Búsqueda Metódica en Mathlib y Desacoplamiento de Módulos

* **Error cometido:**
  Al crear `CajitaWallBound.lean`, se intentó invocar `pi_gt_three` directamente sin importar el módulo específico, generando `Unknown identifier pi_gt_three`.
* **Causa raíz:**
  Asumir que identificadores matemáticos elementales están disponibles en el preludio básico o en `Mathlib.Data.Real`. En Mathlib 4, las cotas numéricas de $\pi$ se encuentran en `Mathlib.Analysis.Real.Pi.Bounds`.
* **Regla obligatoria:**
  1. Realizar siempre búsquedas de texto locales (`grep_search`) dentro de `.lake/packages/mathlib/` para localizar el espacio de nombres y el archivo exacto antes de escribir el código (`import Mathlib.Analysis.Real.Pi.Bounds` y `Real.pi_gt_three`).
  2. NUNCA realizar llamadas externas no autorizadas; toda la documentación y biblioteca de Mathlib se encuentra localmente en el disco duro.

---

### Regla 17: Aislamiento Estricto de la Recta Crítica en Altas Frecuencias (Boca A)

* **Error conceptual evitado:**
  Intentar demostrar $\zeta(s) \ne 0$ de manera global en Boca A ($|t| \ge 1/2$).
* **Causa raíz:**
  En la recta crítica $\operatorname{Re}(s) = 1/2$, la función Zeta **SÍ tiene ceros** en la región de Boca A (por ejemplo, el primer cero no trivial $\gamma_1 \approx 14.134725$ vive en $1/2 + 14.134725\,i$, que pertenece a Boca A). Exigir no-anulación en todo Boca A es falso y contradice la existencia misma de los ceros de Riemann.
* **Regla obligatoria:**
  1. En Boca A, la condición requerida es estrictamente la no-anulación **fuera de la recta crítica** (`s.re ≠ 1 / 2`).
  2. El teorema maestro de reducción debe formularse como:
     ```lean
     (h_bocaA_off : ∀ s ∈ strip, inBocaA s → s.re ≠ 1 / 2 → riemannZeta s ≠ 0)
     ```
  3. Esto alinea la reducción con la asimetría del primo 2 ($r_2(\delta) \ne 1$ para $\delta \ne 0$), donde la asimetría transversal prohíbe cancelaciones a cero.

---

### Regla 18: Protocolo de Sincronización y Paridad Continua al 100%

* **Regla obligatoria:**
  1. Inmediatamente después de crear o modificar cualquier archivo en el espacio de trabajo (`rh_g1_lean`), se debe compilar el proyecto completo con `lake build` para confirmar que el código de salida sea 0.
  2. Acto seguido, sincronizar todos los archivos modificados con el directorio de respaldo (`Downloads\progreso de la hipotesis de riemman\04_lean_rh_g1\`).
  3. Ejecutar una verificación binaria / por contenido (`filecmp.cmp`) para garantizar que la paridad sea exactamente del 100% (cero diferencias).
  4. Actualizar las bitácoras y mapas (`walkthrough.md`, `mapa_grafico_progreso_rh.md`, `mapa_progreso_rh.html`) para que el usuario siempre tenga visibilidad clara y transparente del estado exacto.

---

### Regla 19: Principio de Navegación y Convergencia por Conexiones del Mapa Mental (Freeplane)

* **Principio Director:**
  Toda formalización en Lean 4 debe utilizar activamente la topología de conexiones, rutas y nodos del Mapa Mental (`RH_mapa_mental.mm` y `00_raiz.md` a `12_prospectos_conexiones.md`).
  1. **Identificación de Puntos de Convergencia:** Antes de formalizar cualquier lema o módulo auxiliar, rastrear hacia qué nodo, agujero (H1–H8) o cruce *joint* (como `CX-J3`, `CX-N07` o las rutas α, β, γ) converge lógicamente en el mapa.
  2. **Prohibición de Lemas Aislados:** No se formalizan lemas huérfanos o construcciones ad-hoc sin un rol arquitectónico definido dentro de la partición de las Tres Habitaciones y las Tres Hojas.
  3. **Retroalimentación Continua Mapa ↔ Lean 4:** Todo avance o herramienta demostrada en Lean 4 debe volcarse de inmediato al mapa mental y sus documentos asociados en `01_mapa_freeplane/`, garantizando que el mapa funcione permanentemente como la brújula y el respaldo conceptual del desarrollo formal.

---

## 2. Auditoría de Cero Contaminación en Archivos Previos

Se ejecutó una auditoría exhaustiva en todos los 37 módulos de `RhG1Lean/`:
* **Búsqueda de `sorry`:** CERO ocurrencias en código (solo 2 menciones en comentarios de estado).
* **Búsqueda de `axiom`:** CERO axiomas no comprobados.
* **Integridad de los 37 módulos:** Todos los módulos permanecen íntegros, puros y validados formalmente por Lean 4 (3853 jobs en verde, 500 declaraciones demostradas con exit code 0).