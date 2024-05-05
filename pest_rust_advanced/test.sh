#!/bin/bash

# Test script for building and working examples

# Initialize the counter for passing tests
passing_tests=0

# Build the project
echo "Building the project..."
cargo build --release

# Run the examples
echo "Running the examples..."


### Example 1 ###
echo "Example 1..."
./target/release/vae ../manual_translation/majority_vote/lib/majority_vote.ex

output=$(spin -search -DVECTORSZ=40960 test_out.pml 2>&1)

if echo "$output" | grep -q "errors: 0"; then
    echo "Test passed"
    passing_tests=$((passing_tests + 1))
else
    echo "Test failed: majority vote"
fi


### Example 2 ###
echo "Example 2..."
./target/release/vae ../manual_translation/distributed_calculator/calc.ex

output=$(spin test_out.pml 2>&1)

if echo "$output" | grep -q "2 processes created"; then
    echo "Test passed"
    passing_tests=$((passing_tests + 1))
else
    echo "Test failed: distributed calculator"
fi


### Example 3 ###
echo "Example 3..."
./target/release/vae ../manual_translation/basic_deadlock/basic_deadlock/lib/basic_deadlock.ex

output=$(spin -search -DVECTORSZ=40960 test_out.pml 2>&1)

if echo "$output" | grep -q "errors: 1"; then
    echo "Test passed"
    passing_tests=$((passing_tests + 1))
else
    echo "Test failed: basic deadlock"
fi


### Example 4 ###
echo "Example 4..."
./target/release/vae ../manual_translation/basic_sequential/lib/basic_sequential.ex

output=$(spin test_out.pml 2>&1)

if echo "$output" | grep -q "4 processes created"; then
    echo "Test passed"
    passing_tests=$((passing_tests + 1))
else
    echo "Test failed: basic sequential"
fi

# Report the number of passing tests
echo "Passed: $passing_tests / 4"
