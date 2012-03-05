#!/bin/bash

echo -e "\e[1;31m"
echo -e "***************************************************************"
echo -e "NEGATIVE TESTS"
echo -e "\e[0m"

for FN in `ls $DJS_DIR/tests/djs/*/xx*.js`
do
  echo -n "$FN  "
  ./system-d -djs $FN | tail -1
done

echo -e "\e[1;32m"
echo -e "***************************************************************"
echo -e "POSITIVE TESTS"
echo -e "\e[0m"

for FN in `ls $DJS_DIR/tests/djs/*/[^_x][^_x]*.js`
do
  echo -n "$FN  "
  ./system-d -djs $FN | tail -1
done

