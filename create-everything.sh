#!/bin/bash

everything="Everything.agda"
echo "" >> $everything

find . -type f \
  \( -name '*.agda' ! -name 'index.agda' ! -name 'Everything.agda' ! -path './Experiments/**' \) \
  -print0 | sort -z | while read -d $'\0' file
do
  module=$(echo "$file" | sed -e "s|./||" -e 's|\.agda$||' -e 's|/|.|g')
  echo "import ${module}" >> $everything
done
