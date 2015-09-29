#! /usr/bin/bash

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
  id=$(realpath $1)
  [[ -n ${lib_map[$id]} ]] && exit
  lib_map[$id]=$1

  #local objs=`( grep '^package duck\.' $1; grep '^import ' $1 | grep -v ' scala\.' | grep -v ' leon\.' ) | sed 's/^.*[\. ] *\([^\.]*\)\.[^\.]*$/\1/'`
  local objs=
  IFS=$'\n'
  for dep in $(grep '^import ' $1 | grep -v ' scala\.' | grep -v ' leon\.')
  do
    case "^$dep$" in
      *._$)   obj=$(echo $dep | sed 's/^.*[ \.]\([^\._]\+\)\._.*/\1/') ;;
      *.{*}$) obj=$(echo $dep | sed 's/^.*[ \.]\([^\._]\+\)\.{.*/\1/') ;;
      *)      obj=$(echo $dep | sed 's/^.*[ \.]\([^\._]\+\).*/\1/') ;;
    esac
    #echo -e "obj: $obj \t\tdep: $dep" 1>&2
    objs="$objs $obj"
  done
  unset IFS

  [[ -n $DEBUG_MODE ]] && [[ -n $objs ]] && echo "Resolving symbols [$(echo $objs | tr ' ' ',')] for file $1..." 1>&2

  for obj in $objs
  do
    [[ -n ${obj_map[$obj]} ]] && continue
    local found=
    [[ -n $DEBUG_MODE ]] && echo "Resolving symbol $obj..." 1>&2

    for pattern in "object $obj" "class $obj" "package $obj" "package duck\\.$obj"
    do
      local lib=$(grep -Hw "$pattern" $libs | grep -o '^[^:]*')
      [[ -n $lib ]] && found="$lib $found"
    done
    if [[ -n $found ]]
    then
      obj_map[$obj]=1
      for lib in $found
      do
        lid=$(realpath $lib)
        [[ -n ${lib_map[$lid]} ]] && continue
        [[ -n $DEBUG_MODE ]] && echo "Found dependency $lib for symbol $obj" 1>&2
        find_dep $lib
      done
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
  fi

  id=$(realpath $1)
  if [[ -z ${lib_map[$id]} ]]
  then
    libs="$libs $1"
    find_dep $1
  fi
  shift
done

deps=
for id in ${!lib_map[@]}
do
  deps="$deps ${lib_map[$id]}"
done

command="$LEON_SCRIPT $deps $@"
echo $command 1>&2
bash -e $command
