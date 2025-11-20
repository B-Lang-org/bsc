#!/bin/bash

# Test script for unused import warnings
# Compiles each test and validates expected warnings

BSC="/home/ravi/bluespec/upstream/bsc/inst/bin/bsc"
TEST_DIR="/home/ravi/bluespec/bsc/testsuite/bsc.driver/unused_imports"

cd "$TEST_DIR"

# Compile Helper first
echo "=== Compiling Helper packages ==="
$BSC -u Helper.bsv || exit 1
$BSC -u Helper.bs || exit 1
$BSC -u HelperAlias.bsv || exit 1

echo ""
echo "=== Running Tests ==="
echo ""

# Test 1: UnusedImport - should warn about Helper
echo "Test 1: UnusedImport.bsv (expect warning about Helper)"
$BSC -u UnusedImport.bsv 2>&1 | grep -E "Warning|Helper"

echo ""
echo "Test 1b: UnusedImport.bs (expect warning about Helper)"
$BSC -u UnusedImport.bs 2>&1 | grep -E "Warning|Helper"

# Test 2: ConstructorUse - should NOT warn
echo ""
echo "Test 2: ConstructorUse.bsv (expect NO warning)"
$BSC -u ConstructorUse.bsv 2>&1 | grep -E "Warning|Helper" || echo "✓ No warnings (correct)"

echo ""
echo "Test 2b: ConstructorUse.bs (expect NO warning)"
$BSC -u ConstructorUse.bs 2>&1 | grep -E "Warning|Helper" || echo "✓ No warnings (correct)"

# Test 3: TypeSynonymExpansion - should NOT warn
echo ""
echo "Test 3: TypeSynonymExpansion.bsv (expect NO warning)"
$BSC -u TypeSynonymExpansion.bsv 2>&1 | grep -E "Warning|Helper" || echo "✓ No warnings (correct)"

# Test 4: FunctionReference - should NOT warn
echo ""
echo "Test 4: FunctionReference.bsv (expect NO warning)"
$BSC -u FunctionReference.bsv 2>&1 | grep -E "Warning|Helper" || echo "✓ No warnings (correct)"

# Test 5: FieldAccess - should NOT warn
echo ""
echo "Test 5: FieldAccess.bsv (expect NO warning)"
$BSC -u FieldAccess.bsv 2>&1 | grep -E "Warning|Helper" || echo "✓ No warnings (correct)"

# Test 6: InstanceUse - should NOT warn
echo ""
echo "Test 6: InstanceUse.bsv (expect NO warning)"
$BSC -u InstanceUse.bsv 2>&1 | grep -E "Warning|Helper" || echo "✓ No warnings (correct)"

# Test 7: Reexport - should NOT warn
echo ""
echo "Test 7: Reexport.bsv (expect NO warning)"
$BSC -u Reexport.bsv 2>&1 | grep -E "Warning|Helper" || echo "✓ No warnings (correct)"

# Test 8: ReexportType - should NOT warn
echo ""
echo "Test 8: ReexportType.bsv (expect NO warning)"
$BSC -u ReexportType.bsv 2>&1 | grep -E "Warning|Helper" || echo "✓ No warnings (correct)"

# Test 9: ReexportData - should NOT warn
echo ""
echo "Test 9: ReexportData.bsv (expect NO warning)"
$BSC -u ReexportData.bsv 2>&1 | grep -E "Warning|Helper" || echo "✓ No warnings (correct)"

# Test 10: ReexportFunction - should NOT warn
echo ""
echo "Test 10: ReexportFunction.bsv (expect NO warning)"
$BSC -u ReexportFunction.bsv 2>&1 | grep -E "Warning|Helper" || echo "✓ No warnings (correct)"

# Test 11: TransitiveSynonym - should NOT warn
echo ""
echo "Test 11: TransitiveSynonym.bsv (expect NO warning for HelperAlias or Helper)"
$BSC -u TransitiveSynonym.bsv 2>&1 | grep -E "Warning|Helper" || echo "✓ No warnings (correct)"

echo ""
echo "=== Test Summary ==="
echo "All tests completed. Review output above for any unexpected warnings."
