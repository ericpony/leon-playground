#! /usr/bin/bash

DEBUG_MODE=

[[ -z $LEON_LIB_DIR ]] && LEON_LIB_DIR=$(dirname $0)/library

if [[ ! -d $LEON_LIB_DIR ]]
then
  echo "
Please specify the location of the duck library using
export LEON_LIB_DIR=(absolute path of the library)" 1>&2
  exit 1
fi

[[ -z $LEON_SCRIPT ]] && LEON_SCRIPT=$(which leon 2>/dev/null)

if [[ -z $LEON_SCRIPT ]]
then
  echo "
Please add the location of the leon script to PATH, or specify its path using
export LEON_SCRIPT=(absolute path of the script)" 1>&2
  exit 1
fi

declare -A lib_map
declare -A obj_map

libs=$(find "$LEON_LIB_DIR" -name '*.scala')

function find_dep {
  [[ -n ${lib_map[$1]} ]] && exit
  lib_map[$1]=1

  #local objs=`( grep '^package duck\.' $1; grep '^import ' $1 | grep -v ' scala\.' | grep -v ' leon\.' ) | sed 's/^.*[\. ] *\([^\.]*\)\.[^\.]*$/\1/'`
  local objs=`grep '^import ' $1 | grep -v ' scala\.' | grep -v ' leon\.' | sed 's/^.*[ \.]\([^\._]\+\)[\.]\?[^\.]*$/\1/'`

  [[ -n $DEBUG_MODE ]] && [[ -n $objs ]] && echo "Resolving symbols [$(echo $objs | tr ' ' ',')] for file $1..." 1>&2

  for obj in $objs
  do
    [[ -n ${obj_map[$obj]} ]] && continue
    local found=
    [[ -n $DEBUG_MODE ]] && echo "Resolving symbol $obj..." 1>&2

    for pattern in "object $obj" "class $obj" "package $obj" "package duck\\.$obj"
    do
      local lib=$(grep -Hw "$pattern" $libs | head -n1 | grep -o '^[^:]*')
      [[ -n $lib ]] && found=$lib && break
    done
    if [[ -n $found ]]
    then
      obj_map[$obj]=1
      [[ -n ${lib_map[$found]} ]] && continue
      [[ -n $DEBUG_MODE ]] && echo "Found dependency $found for symbol $obj" 1>&2
      find_dep $found
    else
      echo "[Error] Cannot resolve dependency for '$obj'." 1>&2
      exit 1
    fi
  done
}

while [[ $# -gt 0 ]] && [[ -z $(echo $1 | grep '^-') ]]
do
  if [[ $# -lt 1 ]] || [[ -z $(echo $1 | grep '\.scala$') ]]
  then
    echo "usage: $0 SCALA_FILES... (OPTIONS_FOR_LEON...)" 1>&2
    exit 1
  elif [[ ! -f $1 ]]
  then
    echo "[Error] File $1 does not exist." 1>&2
    exit 1
  elif [[ -n ${lib_map[$1]} ]]
  then
    continue
  fi
  libs="$1 $libs"
  find_dep $1
  shift
done

deps=$(echo ${!lib_map[@]})

command="$LEON_SCRIPT $deps $@"
echo $command 1>&2
bash -e $command
