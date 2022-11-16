file_name=$1
description=$2

echo "###### ${description} ######

int main() {
    return 0;
}" > tests/mine/${file_name}.lat

touch tests/mine/${file_name}.output
code tests/mine/${file_name}.lat tests/mine/${file_name}.output