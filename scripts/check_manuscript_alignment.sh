#!/usr/bin/env bash
set -euo pipefail

project_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$project_root"

manuscript="manuscript/Sequential_learning_theory_aligned.tex"
index="checks/manuscript-label-index.tsv"
work_dir="$(mktemp -d)"
trap 'rm -r "$work_dir"' EXIT

rg -o '\\label\{[^}]+\}' "$manuscript" \
  | sed -E 's/.*\\label\{([^}]+)\}.*/\1/' \
  | sort -u > "$work_dir/manuscript-labels.txt"
tail -n +2 "$index" | cut -f1 | sort > "$work_dir/index-labels.txt"

if ! test -s "$work_dir/manuscript-labels.txt"; then
  echo "No manuscript labels were found." >&2
  exit 1
fi

if test -n "$(uniq -d "$work_dir/index-labels.txt")"; then
  echo "The manuscript index contains duplicate label rows." >&2
  uniq -d "$work_dir/index-labels.txt" >&2
  exit 1
fi

if ! diff -u "$work_dir/manuscript-labels.txt" "$work_dir/index-labels.txt"; then
  echo "The label-to-declaration index is not exhaustive." >&2
  exit 1
fi

rg -o '\\(ref|eqref)\{[^}]+\}' "$manuscript" \
  | sed -E 's/.*\\(ref|eqref)\{([^}]+)\}.*/\2/' \
  | sort -u > "$work_dir/references.txt"
if ! comm -23 "$work_dir/references.txt" "$work_dir/manuscript-labels.txt" \
    > "$work_dir/unresolved-references.txt"; then
  exit 1
fi
if test -s "$work_dir/unresolved-references.txt"; then
  echo "The aligned manuscript contains unresolved references:" >&2
  cat "$work_dir/unresolved-references.txt" >&2
  exit 1
fi

declare -a environment_stack=()
rg -o '\\(begin|end)\{[^}]+\}' "$manuscript" > "$work_dir/environments.txt"
while IFS= read -r token; do
  environment="$(sed -E 's/\\(begin|end)\{([^}]+)\}/\2/' <<< "$token")"
  if [[ "$token" == \\begin* ]]; then
    environment_stack+=("$environment")
  else
    stack_size="${#environment_stack[@]}"
    if (( stack_size == 0 )) || \
        [[ "${environment_stack[stack_size - 1]}" != "$environment" ]]; then
      echo "Unbalanced LaTeX environment at $token." >&2
      exit 1
    fi
    unset 'environment_stack[stack_size - 1]'
  fi
done < "$work_dir/environments.txt"

if (( ${#environment_stack[@]} != 0 )); then
  echo "The aligned manuscript has an unclosed LaTeX environment." >&2
  exit 1
fi

perl -0777 -e '
  $text = <>; $depth = 0;
  for ($i = 0; $i < length($text); $i++) {
    $char = substr($text, $i, 1);
    next unless $char eq "{" || $char eq "}";
    $slashes = 0;
    for ($j = $i - 1; $j >= 0 && substr($text, $j, 1) eq "\\"; $j--) {
      $slashes++;
    }
    next if $slashes % 2 == 1;
    $depth += $char eq "{" ? 1 : -1;
    die "Unmatched closing brace.\n" if $depth < 0;
  }
  die "Unclosed brace.\n" unless $depth == 0;
' "$manuscript"

{
  echo 'import AllResults'
  echo 'import SequentialLearning.ManuscriptAlignment'
  awk -F '\t' 'NR > 1 {
    count = split($4, names, /; /)
    for (i = 1; i <= count; i++) print "#check " names[i]
  }' "$index"
} > "$work_dir/Phase5DeclarationAudit.lean"

lake build SequentialLearning.ManuscriptAlignment
lake env lean "$work_dir/Phase5DeclarationAudit.lean"

if rg --fixed-strings 'Let $g:\mathbb R\to\mathbb R$ be Borel measurable' \
    "$manuscript" >/dev/null; then
  echo "The obsolete global measurability assumption on g remains." >&2
  exit 1
fi

if ! rg --fixed-strings 'Set $g_+(r):=g(\max\{r,0\})$' \
    "$manuscript" >/dev/null; then
  echo "The aligned increasing-loss proof omits the measurable extension." >&2
  exit 1
fi

if rg --fixed-strings 'We restrict attention to model-estimand pairs for which there exists' \
    "$manuscript" >/dev/null; then
  echo "The obsolete greatest-family existence assumption remains." >&2
  exit 1
fi

for required in 'Representation conventions' \
    'Existence of the greatest valid constraint family' \
    'The same estimand under both observation models' \
    'Same-estimand and RCD scope' \
    'conditional flag distribution' \
    'W_{2,d}(\mu,\nu)=W_{2}(\mu_{\mathbb H},\nu_{\mathbb H})'; do
  if ! rg --fixed-strings "$required" "$manuscript" >/dev/null; then
    echo "The aligned manuscript is missing: $required" >&2
    exit 1
  fi
done

if rg --fixed-strings 'coupling-lift condition' "$manuscript" >/dev/null; then
  echo "The obsolete flag-space coupling-lift qualification remains." >&2
  exit 1
fi

echo "Every manuscript label resolves to compiled declarations and all alignment edits are present."
