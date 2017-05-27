#!/bin/sh

version=$(coqc -v | head -n 1 | sed 's@^.* version \([0-9]\.[0-9]\+\).*$@\1@')

case $version in
    8.[34])
        cat <<EOF
Require Omega.
EOF
        ;;

    8.[56])
        cat <<EOF
Require Omega.
Require Export OmegaTactic.
EOF
        echo ''
        ;;
    *)
        echo 'Unknown coq version' 1>&2
        exit 1
        ;;
esac
