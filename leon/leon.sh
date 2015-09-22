#! /usr/bin/bash

[[ -z $LEON_LIB_DIR ]] && LEON_LIB_DIR=$(dirname $0)/library
[[ -z $LEON_SCRIPT ]] && LEON_SCRIPT=$(which leon 2>/dev/null)

if [[ -z $LEON_SCRIPT ]]
then
  echo "
Please add the location of the leon script to PATH, or specify its path using
export LEON_SCRIPT=(absolute path of the script)" 1>&2
  exit 1
fi

if [[ $# -lt 1 ]] || [[ -z $(echo $1 | grep '\.scala$') ]]
then 
  echo "usage: $0 SCALA_FILE [OPTIONS_FOR_LEON]" 1>&2
  exit 1
fi

if [[ ! -f $1 ]]
then
  echo "[Error] File $1 does not exist." 1>&2
  exit 1
fi

declare -A libmap
declare -A objmap

libs=$(echo $1; find "$LEON_LIB_DIR" -name '*.scala')

function find_dep {
  [[ -n ${libmap[$1]} ]] && exit
  local objs=$(grep '^import ' $1 | grep -v ' scala\.' | grep -v ' leon\.' | sed 's/^.*[\. ] *\([^\.]*\)\.[^\.]*$/\1/g')
  libmap[$1]=1

  #echo Resolving $objs for file $1... 1>&2
  for obj in $objs
  do
    [[ -n ${objmap[$obj]} ]] && continue
    local found=
    for pattern in "object $obj" "class $obj" "package $obj" "package duck\\.$obj"
    do
      local lib=$(grep -H "$pattern" $libs | head -n1 | grep -o '^[^:]*')
      [[ -n $lib ]] && found=$lib && break
    done
    if [[ -n $found ]]
    then
      objmap[$obj]=1
      [[ -n ${libmap[$found]} ]] && continue
      find_dep $found
    else
      echo "[Error] Cannot resolve dependency for '$obj'." 1>&2
      exit 1
    fi
  done
}

find_dep $1
deps=$(echo ${!libmap[@]})

shift

command="$LEON_SCRIPT $deps $@"
echo $command 1>&2
bash -e $command
