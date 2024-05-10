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

output=$(./target/release/vae -q -v ../manual_translation/majority_vote/lib/majority_vote.ex 2>&1)

if echo "$output" | grep -q "0 error(s)"; then
    echo "Test passed"
    passing_tests=$((passing_tests + 1))
else
    echo "Test failed: majority vote"
fi


### Example 2 ###
echo "Example 2..."

output=$(./target/release/vae -q -v ../manual_translation/distributed_calculator/calc.ex 2>&1)

if echo "$output" | grep -q "0 error(s)"; then
    echo "Test passed"
    passing_tests=$((passing_tests + 1))
else
    echo "Test failed: distributed calculator"
fi


### Example 3 ###
echo "Example 3..."

output=$(./target/release/vae -q -v ../manual_translation/basic_deadlock/basic_deadlock/lib/basic_deadlock.ex 2>&1)

if echo "$output" | grep -q "1 error(s)"; then
    echo "Test passed"
    passing_tests=$((passing_tests + 1))
else
    echo "Test failed: basic deadlock"
fi


### Example 4 ###
echo "Example 4..."

output=$(./target/release/vae -q -v ../manual_translation/basic_sequential/lib/basic_sequential.ex 2>&1)

if echo "$output" | grep -q "0 error(s)"; then
    echo "Test passed"
    passing_tests=$((passing_tests + 1))
else
    echo "Test failed: basic sequential"
fi

### Example 5 ###
echo "Example 5..."

output=$(./target/release/vae -q -v ../manual_translation/wrong_message_order/lib/wrong_message_order.ex 2>&1)

if echo "$output" | grep -q "0 error(s)"; then
    echo "Test passed"
    passing_tests=$((passing_tests + 1))
else
    echo "Test failed: wrong message order"
fi

### Example 6 ###
echo "Example 6..."

output=$(./target/release/vae -q -v ../manual_translation/basic_array/lib/basic_array.ex 2>&1)

if echo "$output" | grep -q "0 error(s)"; then
    echo "Test passed"
    passing_tests=$((passing_tests + 1))
else
    echo "Test failed: basic array"
fi

# Report the number of passing tests
echo "Passed: $passing_tests / 6"
