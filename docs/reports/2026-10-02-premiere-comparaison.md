# Première comparaison baguette / Chuffed / GCS sur le corpus MiniZinc Challenge

*2026-10-02. Rapport de synthèse ; les chiffres bruts et leur provenance sont dans
`docs/DECISIONS.md` D-0081 (pilote et mise en place) et D-0089 (les cinq runs).*

## Ce qui a été comparé

436 instances : chaque modèle `.mzn` du corpus MiniZinc Challenge 2008–2026 avec son
plus petit fichier de données, appariement épinglé par `bench/corpus/answers.tsv`.
Trois solveurs, chacun aplatissant avec **sa propre** bibliothèque MiniZinc, 300 s de
temps de résolution, 32 Go d'espace d'adressage par processus, sur `fataepyc-07`
(192 cœurs). Les annotations de recherche du modèle sont honorées par les trois ; pas de
recherche libre, pas de redémarrages.

| Solveur | Version | Preuves | Checker |
|---|---|---|---|
| baguette | `main` à `9ff90da`, binaire `8b8d4718…` | VeriPB 3.0, toujours | veripb 3.0.2 (Rust) |
| Chuffed | 0.14.0, bundle MiniZinc 2.10.1 | aucune | — |
| GCS | commit `5882c294` (CP2026-1817), `--prove`, plafond 16 Go par fichier | VeriPB 3.0 | veripb 3.0.2 (Rust) |

Le harnais (`scripts/compare_run.sh`, M6-T4) vérifie chaque preuve produite et confronte
les réponses : un **désaccord** sur SAT/UNSAT, sur un optimum prouvé, ou avec une réponse
épinglée est signalé en tête de rapport. C'est le premier oracle externe de baguette.

## Résultats

### Correction

- **0 désaccord** sur les 127 instances où au moins deux solveurs ont répondu, **0 écart**
  avec les réponses épinglées.
- baguette : **83 preuves vérifiées, 0 rejetée** sur ce run ; 353 preuves vérifiées sur
  la journée sans un rejet.
- GCS : 46 preuves vérifiées, **15 rejetées**, 32 au-delà des 900 s de vérification,
  1 plantage du checker. Les 16 cas problématiques sont tous des optima que Chuffed
  confirme : c'est un résultat sur le proof logging de GCS ou sur le checker, pas sur ses
  réponses. Rapport séparé : `docs/reports/2026-10-02-gcs-rejected-proofs.md`.

### Couverture, sur 436

| Statut | baguette | Chuffed | GCS avec preuves |
|---|---|---|---|
| Résolues (SAT / UNSAT / OPT) | **84** (21 / 5 / 58) | **272** (44 / 10 / 218) | **94** (29 / 6 / 59) |
| Timeout 300 s | 258 | 139 | 40 |
| Plafond de preuve 16 Go | 0 | 0 | **273** |
| Refus (domaines larges, D-0028) | 67 | 0 | 0 |
| Erreur | 2 | 0 | 4 |
| Entrée (pas de données / échec d'aplatissement) | 25 | 25 | 25 |

GCS sans preuves résout 149 instances (D-0081). Baguette passait de 58 à 81 résolues
entre les vagues 30 et 35 du projet, sans rien perdre.

### Vitesse, sur les 51 instances que les trois résolvent

Moyenne arithmétique et **géomoyenne décalée de 1** (exp de la moyenne des log(1 + x),
moins 1 ; l'unité est celle de x). PAR2 sur les 436 : une instance non résolue compte
600 s.

| Solveur | Temps moyen | Temps, géomoyenne +1 | PAR2 sur 436 | Preuve moyenne | Preuve, géomoyenne +1 | Vérification moyenne | Vérification, géomoyenne +1 |
|---|---|---|---|---|---|---|---|
| baguette | 33,5 s | **7,26 s** | 492,6 | 105 Mo | 8,5 Mo | 14,0 s | 2,33 s |
| Chuffed | 0,26 s | **0,20 s** | 240,5 | — | — | — | — |
| GCS | 17,0 s | **2,28 s** | 478,9 | 1 101 Mo | 35,7 Mo | 53,8 s | 6,62 s |

Les colonnes de vérification ne comptent que les preuves vérifiées : 50 sur 51 pour
baguette, 42 sur 51 pour GCS (les 9 autres sont des rejets ou des vérifications au-delà
de 900 s), ce qui avantage GCS dans cette colonne. La moyenne des tailles de preuve de GCS
est dominée par quelques fichiers de plusieurs Go ; la géomoyenne est la comparaison
honnête, et elle dit un facteur 4 en faveur de baguette.

Sur les paires d'instances résolues par les deux solveurs, hors ensemble commun aux trois :

| Paire | Instances | Temps moyen | Temps, géomoyenne +1 |
|---|---|---|---|
| baguette / Chuffed | 84 | 42,4 s / 1,15 s | 9,35 s / 0,40 s |
| baguette / GCS | 51 | 33,5 s / 17,0 s | 7,26 s / 2,28 s |

## Ce qu'il faut en retenir

1. **Baguette est correct là où il répond.** L'oracle externe n'a rien trouvé, et toutes
   ses preuves passent. Les 26 preuves que le checker rejetait la veille, invisibles tant
   que les instances tombaient en timeout, sont corrigées et revérifiées (D-0084).
2. **Le PAR2 de baguette est à 3 % de celui de GCS avec preuves**, les deux au double de
   Chuffed. Sur les instances communes, en géomoyenne décalée, baguette reste à 36×
   Chuffed et 3,2× GCS ; en moyenne arithmétique, à 2× GCS, parce que les instances
   longues de GCS pèsent lourd. Le travail de la semaine a multiplié les nœuds par seconde par environ 7
   (`falsified_at`), puis par 2 à 6 selon les modèles (mémo de `Justify`, index de la
   trail, `Trace.position_of`) ; ces derniers gains ne sont **pas** dans les chiffres
   ci-dessus, mesurés sur le binaire `9ff90da`.
3. **Les preuves de baguette sont un point fort** : quatre fois plus petites que celles de
   GCS en géomoyenne, dix fois en moyenne, et vérifiées trois à quatre fois plus vite. En contrepartie, 12 instances résolues ont une
   preuve que veripb ne vérifie pas en 900 s, et GCS plafonne à 16 Go sur 273 instances :
   la taille des preuves est le coût commun du proof logging CP, et les hints RUP (M4-T5)
   sont la row qui ferait bouger la colonne de vérification.
4. **Le mur des domaines larges** (67 refus, largeurs de 10 000 à 78 millions) est celui
   de l'encodage d'ordre (D-0028) ; un encodage différent des domaines larges est une
   décision non prise.

## Réserves de lecture

- Les colonnes `TIMEOUT` de Chuffed et GCS viennent d'un run où le nœud portait aussi un
  sweep de 64 jobs ; elles sont légèrement pessimistes.
- Le shim `mznlib/compat_mzn1.mzn` (syntaxe MiniZinc 1.x des modèles 2008–2010) a été
  passé en second fichier à **tous** les aplatissements Chuffed et GCS, pas seulement aux
  modèles 1.x. Il ne définit que des annotations et le `global_cardinality` à deux
  arguments ; `COMPAT=0` donne le comportement strict.
- 25 instances n'atteignent aucun solveur : 20 sans fichier de données, 4 modèles que
  MiniZinc 2.10.1 refuse, 1 aplatissement au-delà de 120 s.

## Prochaines mesures

Un nouveau run `--time-limit` et une nouvelle comparaison sur le binaire final de la
semaine (après M6-T14, M6-T15, M6-T16) ; le rapport aux auteurs de GCS ; les hints RUP.
