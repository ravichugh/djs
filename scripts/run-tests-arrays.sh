#!/bin/bash

echo -e "\e[1;32m"
echo -e "***************************************************************"
echo -e "POSITIVE TESTS"
echo -e "\e[0m"

for FN in `ls $DJS_DIR/tests/functional/arrays/[^a][^r][^r]*.ml`
do
  echo -n "$FN  "
  ./system-d $FN | tail -1
done

