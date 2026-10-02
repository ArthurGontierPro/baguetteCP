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

Statistique : la **géomoyenne décalée de 1**, exp de la moyenne des log(1 + x) moins 1,
dans l'unité de x ; ni une instance à 0,01 s ni une à 299 s ne peut la dominer. PAR2 sur
les 436 : une instance non résolue compte 600 s.

| Solveur | Temps (géomoyenne +1) | PAR2 sur 436 | Preuve (géomoyenne +1) | Vérification (géomoyenne +1) | Preuves vérifiées |
|---|---|---|---|---|---|
| baguette | **7,26 s** | 492,6 | 8,5 Mo | 2,33 s | 50 / 51 |
| Chuffed | **0,20 s** | 240,5 | — | — | — |
| GCS | **2,28 s** | 478,9 | 35,7 Mo | 6,62 s | 42 / 51 |

La colonne de vérification ne compte que les preuves vérifiées ; les 9 preuves GCS
manquantes sont des rejets ou des vérifications au-delà de 900 s, ce qui avantage GCS
dans cette colonne.

Sur les paires d'instances résolues par les deux solveurs, hors ensemble commun aux trois :

| Paire | Instances | Temps (géomoyenne +1) |
|---|---|---|
| baguette / Chuffed | 84 | 9,35 s / 0,40 s |
| baguette / GCS | 51 | 7,26 s / 2,28 s |

## Ce qu'il faut en retenir

1. **Baguette est correct là où il répond.** L'oracle externe n'a rien trouvé, et toutes
   ses preuves passent. Les 26 preuves que le checker rejetait la veille, invisibles tant
   que les instances tombaient en timeout, sont corrigées et revérifiées (D-0084).
2. **Le PAR2 de baguette est à 3 % de celui de GCS avec preuves**, les deux au double de
   Chuffed. Sur les instances communes, en géomoyenne décalée, baguette reste à 36×
   Chuffed et 3,2× GCS. Le travail de la semaine a multiplié les nœuds par seconde par environ 7
   (`falsified_at`), puis par 2 à 6 selon les modèles (mémo de `Justify`, index de la
   trail, `Trace.position_of`) ; ces derniers gains ne sont **pas** dans les chiffres
   ci-dessus, mesurés sur le binaire `9ff90da`.
3. **Les preuves de baguette sont un point fort** : quatre fois plus petites que celles de
   GCS en géomoyenne, et vérifiées près de trois fois plus vite. En contrepartie, 12 instances résolues ont une
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

## Pourquoi les preuves de GCS sont plus grosses : un cas mesuré

`2014_stochastic-fjsp … det` (optimum 242 pour les deux), rejoué sur le nœud avec les
statistiques de GCS (`-s`), avec et sans `--prove` :

| | baguette | GCS |
|---|---|---|
| nœuds | 178 (52 conflits, apprentissage de clauses) | **3 007 079** (3 006 955 échecs, pas d'apprentissage, 0 redémarrage) |
| propagations | — | 308,6 M, dont 67,6 M effectives |
| temps | 3,4 s | 72,7 s sans preuve, **193,7 s avec** (×2,7) |
| `.pbp` | 1,53 Mo, 5 717 lignes | 13,93 Go, 192 365 107 lignes |
| par nœud | 8,6 Ko, 32 lignes de 216 o | 4,6 Ko, 64 lignes de 67 o |
| par propagation effective | — | 2,85 lignes (`pol` + `rup` + `del`) |

Sur cette instance la taille vient d'abord de l'arbre : GCS visite 17 000 fois plus de
nœuds, parce qu'il n'apprend pas de nogoods là où baguette ferme la recherche en 52
conflits. Par nœud, la preuve de GCS est en fait plus **petite** en octets que celle de
baguette (ses lignes sont courtes, son encodage binaire tient dans l'`.opb`), mais il
justifie chaque propagation effective au moment où elle a lieu, environ trois lignes
chacune, là où baguette n'écrit une ligne de trace que pour une branche qui échoue. Le
proof logging coûte à GCS un facteur 2,7 en temps ici. Sur le corpus, le facteur 4 en
géomoyenne mélange ces deux effets ; il est le plus fort là où l'apprentissage paie.

## Prochaines mesures

Un nouveau run `--time-limit` et une nouvelle comparaison sur le binaire final de la
semaine (après M6-T14, M6-T15, M6-T16) ; le rapport aux auteurs de GCS ; les hints RUP.
