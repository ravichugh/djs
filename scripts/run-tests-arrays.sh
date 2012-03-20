#!/bin/bash

echo -e "\e[1;32m"
echo -e "***************************************************************"
echo -e "POSITIVE TESTS"
echo -e "\e[0m"

for FN in `ls $DJS_DIR/tests/functional/arrays/[^_][^_]*.ml`
do
  echo -n "$FN  "
  ./system-d $FN | tail -1
done

for FN in `ls $DJS_DIR/tests/imperative/arrays/[^_][^_]*.ml`
do
  echo -n "$FN  "
  ./system-d $FN | tail -1
done

