#!/usr/bin/env bash

set -e

function usage {
    echo "$0 [-h|--help] [-v|--verbose] [-s|--skip-logging] [-p|--package <crate>] <description...>"
    echo
    echo "Profiles a single 'cargo verus verify -p <crate>' run and appends the"
    echo "result to timing_tracker/. <description> is a required free-text note on"
    echo "what changed since the last profiling run (e.g. 'closed up Pending and"
    echo "Committed') -- it becomes the new summary.md entry's header bullet, so"
    echo "there's no separate manual edit step afterwards."
    echo
    echo "<crate> defaults to 'abd', which is what every historical entry in"
    echo "summary.md tracks (it's where the interesting invariant/lemma complexity"
    echo "lives). Bare 'cargo verus verify' (no -p) checks the whole workspace and"
    echo "makes for a noisier, harder-to-compare-over-time report; --workspace"
    echo "verifies nothing at all silently (see claude-docs/PROFILING.md) -- always"
    echo "scope this to one crate."
    echo
    echo "Also prints a regression check against the previous logged run's total"
    echo "verification time."
}
options=$(getopt -l "help,verbose,skip-logging,package:" -o "hvsp:" -a -- "$@")

eval set -- "$options"

LOG=1
PACKAGE="abd"
status=0
while true
do
    case "$1" in
        -h|--help)
            usage
            exit $status
            ;;
        -s|--skip-logging)
            LOG=0
            ;;
        -p|--package)
            PACKAGE="$2"
            shift
            ;;
        -v|--verbose)
            set -x
            ;;
        --)
            shift
            break
            ;;
    esac
    shift
done

DESCRIPTION="$*"
if [ ${LOG} -eq 1 ] && [ -z "${DESCRIPTION}" ];
then
    echo "error: <description> is required (a one-line note on what changed)" >&2
    echo "       pass -s/--skip-logging for a scratch run that skips the log entirely" >&2
    usage
    exit 1
fi

SCRIPT_DIR=$(dirname "$(readlink -f "$0")")
PROJECT_ROOT=$(dirname ${SCRIPT_DIR})

function get_log_id() {
    local ls_output
    ls_output=$(ls ${PROJECT_ROOT}/timing_tracker/*.json 2>/dev/null || true)
    local awk_input="0000"
    for file in ${ls_output};
    do
        local b
        b=$(basename ${file} | cut -d_ -f1)
        awk_input="${awk_input}\n${b}"
    done

    awk -F'\n' 'BEGIN { max = 0}; { if ($0 > max) { max = $0 } }; END { printf "%04d\n", max+1 }' <(echo -e ${awk_input})
}

pushd ${PROJECT_ROOT} >/dev/null

log_id=$(get_log_id)
log_name="${log_id}_$(date +'%Y_%m_%d_%H_%M_%S').json"
log_filename="timing_tracker/${log_name}"

# A single verification run, not two: `--output-json` goes to stdout (captured
# straight to the log file) and `/usr/bin/time -v`'s own report goes to stderr
# (captured separately, to pull the true end-to-end wall clock -- this includes
# cargo/rustc frontend overhead before verus's own internal timer starts, which
# the JSON's "total" field does not, so it's a genuinely different number worth
# keeping, not a duplicate of it).
#
# The previous version of this script ran `cargo verus verify` twice -- once for
# the JSON, once more under `/usr/bin/time -v` -- doubling the cost of every
# profiling run. That's almost certainly why profiling fell out of habitual use;
# a single run removes the excuse.
time_stderr=$(mktemp)
trap 'rm -f "${time_stderr}"' EXIT

# Cargo only re-invokes rustc (and so verus) for a crate whose fingerprint it
# thinks changed since the last build, and that fingerprint is content-hash
# based, not mtime based -- `touch`ing a source file does NOT invalidate it.
# Profiling twice in a row with nothing edited in between (e.g. re-running
# right after `just verify`, or re-running this script itself) hits that
# cache: cargo reports "Finished ... in 0.2Xs" and prints NOTHING to stdout,
# so `--output-json` silently produces an EMPTY log file instead of an error.
# `cargo clean -p <crate>` forces a real rebuild (and so a real, fresh
# verification pass) every time -- a few extra seconds, but a cached skip is a
# wasted run, not a valid data point, which is the whole point of a profiler.
cargo clean -p "${PACKAGE}" >/dev/null 2>&1 || true

if [ ${LOG} -eq 1 ];
then
    /usr/bin/time -v cargo verus verify -p "${PACKAGE}" -- \
        --triggers-mode silent \
        --time-expanded \
        --output-json > ${log_filename} 2> "${time_stderr}"
else
    /usr/bin/time -v cargo verus verify -p "${PACKAGE}" -- \
        --triggers-mode silent \
        --time-expanded 2> "${time_stderr}"
fi

cat "${time_stderr}" >&2

ELAPSED_TIME='Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): '
ELAPSED_AWK_PROGRAM="/${ELAPSED_TIME}/ { print \$2 }"
time_reported=$(awk -F': ' "${ELAPSED_AWK_PROGRAM}" < "${time_stderr}")

json_object_count=0
if [ -s ${log_filename} ];
then
    json_object_count=$(jq -s 'length' < ${log_filename})
fi

if [ ${LOG} -eq 1 ] && [ "${json_object_count}" -gt 0 ];
then
    stats_table=$(${SCRIPT_DIR}/print_profile_stats.sh --package "${PACKAGE}" --kv "elapsed wall clock|${time_reported}" ${log_filename})
    echo "${stats_table}"

    # Regression check against the previous logged run (if any): compare verus's
    # own internally-measured total, which is the number both this table and
    # summary.md's history have always tracked. `-p <crate>` can emit more than
    # one JSON object per run (one per already-verified dependency crate it also
    # checks) -- `jq -s '.[-1]'` takes the last one, which is always the crate
    # actually requested (see print_profile_stats.sh's comment for why).
    #
    # Caveat: this compares raw wall-clock ms with no hostname/hardware check.
    # If the previous entry's "hostname" row (in the printed table, not
    # tracked in this comparison) differs from this run's, a delta here
    # reflects different hardware, not a real regression -- eyeball the
    # hostname before trusting a WARNING below.
    prev_json=$(ls -1 ${PROJECT_ROOT}/timing_tracker/*.json 2>/dev/null \
        | grep -v "/${log_name}$" | sort | tail -n1 || true)
    if [ -n "${prev_json}" ];
    then
        prev_total=$(jq -s '.[-1]."times-ms"."total"' < "${prev_json}")
        new_total=$(jq -s '.[-1]."times-ms"."total"' < "${log_filename}")
        delta_pct=$(awk -v a="${prev_total}" -v b="${new_total}" \
            'BEGIN { printf "%+.1f", (b - a) / a * 100 }')
        echo
        echo "total (wall-clock) vs previous entry ($(basename ${prev_json})): ${prev_total}ms -> ${new_total}ms (${delta_pct}%)"
        regression_threshold_pct=15
        if awk -v d="${delta_pct}" -v t="${regression_threshold_pct}" 'BEGIN { exit !(d > t) }';
        then
            echo "WARNING: total verification time regressed by more than ${regression_threshold_pct}% -- investigate before committing."
        fi
    fi

    {
        echo "# ${log_id}: $(date +'%Y-%m-%d %H:%M:%S')"
        echo
        echo "- ${DESCRIPTION}"
        echo
        echo "${stats_table}"
        echo
        echo "---"
        echo
        cat timing_tracker/summary.md 2>/dev/null
    } > timing_tracker/summary.md.new
    mv timing_tracker/summary.md.new timing_tracker/summary.md

    echo
    echo "logged as timing_tracker/${log_name}, prepended to timing_tracker/summary.md"
elif [ ${LOG} -eq 1 ];
then
    rm -f ${log_filename}
    echo "error: verification produced no --output-json data (empty log file)." >&2
    echo "       nothing was written to timing_tracker/ or summary.md." >&2
    exit 1
fi

popd >/dev/null
