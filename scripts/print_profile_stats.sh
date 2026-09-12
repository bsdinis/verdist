#!/usr/bin/env bash

set -e

function usage {
    echo "$0 [-h|--help] [-v|--verbose] [-p|--package <name>] [--kv|-k \"<key>|<value>\"]* <file>"
    echo
    echo "<file> is the --output-json stream from 'cargo verus verify -p <crate> ...'."
    echo "Since <crate> may pull in already-verified dependency crates, cargo-verus"
    echo "prints one JSON object per crate it actually checks, concatenated in build"
    echo "(i.e. dependency) order -- the LAST object in the stream is always the crate"
    echo "that was actually requested via -p, since it depends on everything checked"
    echo "before it. This script reports on that last object only."
}
options=$(getopt -l "help,verbose,kv:,package:" -o "hvk:p:" -a -- "$@")

eval set -- "$options"

KV_PAIRS=()
PACKAGE=""
status=0
while true
do
    case "$1" in
        -h|--help)
            usage
            exit $status
            ;;
        -v|--verbose)
            set -x
            ;;
        -k|--kv)
            KV_PAIRS+=("$2")
            shift # shift value too
            ;;
        -p|--package)
            PACKAGE="$2"
            shift
            ;;
        --)
            shift
            break
            ;;
    esac
    shift
done

FILENAME=$1
if [ -z "$FILENAME" ];
then
    usage
    exit 1
elif ! [ -r "${FILENAME}" ];
then
    echo "file not found: ${FILENAME}"
    exit 1
fi

SCRIPT_DIR=$(dirname "$(readlink -f "$0")")
PROJECT_ROOT=$(dirname ${SCRIPT_DIR})

pushd ${PROJECT_ROOT} >/dev/null

# `cargo verus verify -p <crate> --output-json` emits one JSON object per crate
# it ends up checking (the requested crate plus any already-verified dependency
# crates it pulls in), concatenated with no separator -- jq reads each
# whitespace-separated top-level value in a stream independently by default,
# so a naive `jq '.foo' < file` silently returns one line PER object instead of
# one, producing garbled/duplicated output once the workspace has more than one
# verified crate in a dependency chain. `jq -s` slurps the whole stream into an
# array first; `.[-1]` takes the last element, which is always the actually-
# requested crate (dependencies verify before it, never after).
report=$(jq -s '.[-1]' < ${FILENAME})

verus_profile=$(jq -r '."verus"."profile"' <<< "${report}")
verus_version=$(jq -r '."verus"."version"' <<< "${report}")
verus_platform_os=$(jq -r '."verus"."platform"."os"' <<< "${report}")
verus_arch=$(jq -r '."verus"."platform"."arch"' <<< "${report}")
verus_platform="${verus_platform_os}_${verus_arch}"
rust_toolchain=$(jq -r '."verus"."toolchain"' <<< "${report}")
verus_commit=$(jq -r '."verus"."commit"' <<< "${report}")
num_threads=$(jq '."times-ms"."num-threads"' <<< "${report}")
total_ms=$(jq '."times-ms"."total"' <<< "${report}")
cpu_time_ms=$(jq '."times-ms"."estimated-cpu-time"' <<< "${report}")
verification_wall_clock_ms=$(jq '."times-ms"."verification"."total"' <<< "${report}")
verification_cpu_ms=$(jq '."times-ms"."total-verify"' <<< "${report}")
smt_run_ms=$(jq '."times-ms"."smt"."smt-run"' <<< "${report}")
verified_count=$(jq '."verification-results"."verified"' <<< "${report}")
sorted_modules=$(jq '."times-ms"."total-verify-module-times" | sort_by(.time)' <<< "${report}")

printf "| %35s | %37s    |\n" "" ""
printf "|---|---|\n"
if [ -n "${PACKAGE}" ];
then
    printf "| %35s | %37s    |\n" "package" "${PACKAGE}"
fi
printf "| %35s | %37s    |\n" "profile" ${verus_profile}
printf "| %35s | %37s    |\n" "version" ${verus_version}
printf "| %35s | %37s    |\n" "platform" ${verus_platform}
printf "| %35s | %37s    |\n" "toolchain" ${rust_toolchain}
printf "| %35s | %39s |\n" "verus commit" ${verus_commit}
printf "| %35s | %37s    |\n" "hostname" "$(hostname)"
printf "| %35s | %37s    |\n" "n_threads" ${num_threads}
printf "| %35s | %37s    |\n" "verified" ${verified_count}
printf "| %35s | %37s ms |\n" "total (wall-clock)" ${total_ms}
printf "| %35s | %37s ms |\n" "total (cpu)" ${cpu_time_ms}
printf "| %35s | %37s ms |\n" "verification (wall-clock)" ${verification_wall_clock_ms}
printf "| %35s | %37s ms |\n" "verification (cpu)" ${verification_cpu_ms}
printf "| %35s | %37s ms |\n" "smt run (cpu)" ${smt_run_ms}

for n in {1..5};
do
    module=$(jq ".[-$n]" <<< "${sorted_modules}")
    name=$(jq -r '."module"' <<< "${module}")
    time=$(jq '."time"' <<< "${module}")
    printf "| %35s | %37s ms |\n" "${name}" "${time}"
done


for kv in "${KV_PAIRS[@]}";
do
    k=$(echo $kv | cut -d'|' -f 1)
    v=$(echo $kv | cut -d'|' -f 2)
    printf "| %35s | %37s    |\n" "${k}" "${v}"
done

popd >/dev/null
