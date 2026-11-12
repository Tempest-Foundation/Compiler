#!/bin/sh
set -eu

compiler=$1
c_compiler=$2
llc=$3
work_dir=$4
fixture_dir=$5
features="$fixture_dir/features.sl"

mkdir -p "$work_dir"

"$compiler" "$fixture_dir/generic_constraints.sl" --build.compile-only \
	"--build.output=$work_dir/generic_constraints.o"

compile_ir() {
	target=$1
	opt=$2
	out=$3
	"$compiler" "$features" --emit.ir "--opt.level=$opt" "--tar.triple=$target" \
		"--build.output=$out"
}

ir_instructions() {
	ir_file=$1
	function=$2
	awk -v fn="$function" '
		$0 ~ "^define .*@" fn "\\(" { active = 1; next }
		active && /^}/ { exit }
		active {
			line = $0
			if (line ~ /^[[:space:]]*[A-Za-z0-9_.-]+:[[:space:]]*$/) next
			if (line ~ /^[[:space:]]*$/) next
			gsub(/%[A-Za-z0-9$._-]+/, "%v", line)
			sub(/^[[:space:]]+/, "", line)
			print line
		}' "$ir_file"
}

asm_instructions() {
	asm_file=$1
	function=$2
	awk -v fn="$function" '
		$0 ~ "^" fn ":" { active = 1; next }
		active && /^[A-Za-z_.$][A-Za-z0-9_.$]*:[[:space:]]*$/ { exit }
		active {
			line = $0
			sub(/#.*/, "", line)
			if (line !~ /^[[:space:]]*[A-Za-z][A-Za-z0-9_.]*([[:space:]]|$)/) next
			gsub(/%[A-Za-z][A-Za-z0-9]*/, "%reg", line)
			gsub(/\$[0-9]+/, "$imm", line)
			gsub(/#[0-9]+/, "#imm", line)
			gsub(/[[:space:]]+/, " ", line)
			sub(/^ /, "", line)
			sub(/ $/, "", line)
			print line
		}' "$asm_file"
}

assert_same_ir() {
	ir_file=$1
	left=$2
	right=$3
	if [ "$(ir_instructions "$ir_file" "$left")" != \
		"$(ir_instructions "$ir_file" "$right")" ]; then
		echo "unoptimized/optimized IR differs for $left and $right in $ir_file" >&2
		ir_instructions "$ir_file" "$left" >&2
		ir_instructions "$ir_file" "$right" >&2
		exit 1
	fi
}

assert_same_asm() {
	asm_file=$1
	left=$2
	right=$3
	if [ "$(asm_instructions "$asm_file" "$left")" != \
		"$(asm_instructions "$asm_file" "$right")" ]; then
		echo "generated instructions differ for $left and $right in $asm_file" >&2
		asm_instructions "$asm_file" "$left" >&2
		asm_instructions "$asm_file" "$right" >&2
		exit 1
	fi
}

expect_return() {
	ir_file=$1
	function=$2
	return_value=$3
	if ! ir_instructions "$ir_file" "$function" | grep -Fqx "ret $return_value"; then
		echo "$function did not fold to '$return_value' in $ir_file" >&2
		ir_instructions "$ir_file" "$function" >&2
		exit 1
	fi
}

expect_failure() {
	input=$1
	name=$2
	shift 2
	log_file="$work_dir/$name.log"
	if "$compiler" "$input" --build.compile-only "--build.output=$work_dir/$name.o" \
		>"$log_file" 2>&1; then
		echo "expected $input to fail compilation" >&2
		exit 1
	fi
	for diagnostic in "$@"; do
		if ! grep -Fq "$diagnostic" "$log_file"; then
			echo "missing diagnostic '$diagnostic' for $input" >&2
			cat "$log_file" >&2
			exit 1
		fi
	done
}

check_ir_file() {
	ir_file=$1
	for intrinsic in uadd.sat.i8 usub.sat.i8 sadd.sat.i8 ssub.sat.i8 \
		uadd.sat.i129 usub.sat.i129 sadd.sat.i129 ssub.sat.i129; do
		if ! grep -Fq "@llvm.$intrinsic" "$ir_file"; then
			echo "missing LLVM saturation intrinsic llvm.$intrinsic in $ir_file" >&2
			exit 1
		fi
	done
	if ! awk '/^[[:space:]]*(tail )?call / && $0 !~ /@llvm\./ { print; failed = 1 }
		END { exit failed }' "$ir_file"; then
		echo "non-intrinsic call found in generated IR $ir_file" >&2
		exit 1
	fi
	for function in sat_add_constant wrap_add_constant sat_add_signed_constant \
		sat_sub_signed_constant sat_add_u129_constant wrap_add_u129_constant; do
		case $function in
			sat_add_constant) expected='i8 -1' ;;
			wrap_add_constant) expected='i8 14' ;;
			sat_add_signed_constant) expected='i8 127' ;;
			sat_sub_signed_constant) expected='i8 -128' ;;
			sat_add_u129_constant) expected='i129 -1' ;;
			wrap_add_u129_constant) expected='i129 0' ;;
		esac
		expect_return "$ir_file" "$function" "$expected"
	done
}

x86_target=x86_64-unknown-linux-gnu
arm_target=aarch64-unknown-linux-gnu
x86_o0="$work_dir/features.x86.o0.ll"
x86_o2="$work_dir/features.x86.o2.ll"
arm_o0="$work_dir/features.arm.o0.ll"
arm_o2="$work_dir/features.arm.o2.ll"
arm_supported=no
if "$llc" --version | grep -Eiq '^[[:space:]]*aarch64[[:space:]]'; then
	arm_supported=yes
fi
compile_ir "$x86_target" none "$x86_o0"
compile_ir "$x86_target" high "$x86_o2"
if [ "$arm_supported" = yes ]; then
	compile_ir "$arm_target" none "$arm_o0"
	compile_ir "$arm_target" high "$arm_o2"
fi

check_ir_file "$x86_o0"
check_ir_file "$x86_o2"
if [ "$arm_supported" = yes ]; then
	check_ir_file "$arm_o0"
	check_ir_file "$arm_o2"
fi

for ir_file in "$x86_o0" "$x86_o2"; do
	assert_same_ir "$ir_file" range_extract range_extract_manual
	assert_same_ir "$ir_file" wrap_add plain_add
	assert_same_ir "$ir_file" wrap_precedence plain_precedence
	assert_same_ir "$ir_file" wrap_sub plain_sub
done

ufcs_ir="$work_dir/ufcs.ll"
"$compiler" "$fixture_dir/ufcs.sl" --emit.ir --opt.level=none "--tar.triple=$x86_target" \
	"--build.output=$ufcs_ir"
assert_same_ir "$ufcs_ir" test_ufcs_direct test_direct_call
assert_same_ir "$ufcs_ir" test_ufcs_chain test_direct_chain
if [ "$arm_supported" = yes ]; then
	for ir_file in "$arm_o0" "$arm_o2"; do
		assert_same_ir "$ir_file" range_extract range_extract_manual
		assert_same_ir "$ir_file" wrap_add plain_add
		assert_same_ir "$ir_file" wrap_precedence plain_precedence
		assert_same_ir "$ir_file" wrap_sub plain_sub
	done
fi

for opt in 0 2; do
	for arch in x86 arm; do
		if [ "$arch" = arm ] && [ "$arm_supported" != yes ]; then
			continue
		fi
		if [ "$arch" = x86 ]; then
			ir_file=$x86_o0
			[ "$opt" = 0 ] || ir_file=$x86_o2
		else
			ir_file=$arm_o0
			[ "$opt" = 0 ] || ir_file=$arm_o2
		fi
		asm_file="$work_dir/features.$arch.o$opt.s"
		"$llc" "-O=$opt" -filetype=asm "$ir_file" -o "$asm_file"
		assert_same_asm "$asm_file" range_extract range_extract_manual
		assert_same_asm "$asm_file" wrap_add plain_add
		assert_same_asm "$asm_file" wrap_precedence plain_precedence
		assert_same_asm "$asm_file" wrap_sub plain_sub
		if [ "$arch" = x86 ]; then
			call_pattern='^[[:space:]]*callq?[[:space:]]'
		else
			call_pattern='^[[:space:]]*(bl|blr)[[:space:]]'
		fi
		if grep -Eq "$call_pattern" "$asm_file"; then
			echo "generated helper call found in $asm_file" >&2
			grep -En "$call_pattern" "$asm_file" >&2
			exit 1
		fi
	done
done

# A layout annotation is a compile-time assertion. Removing those annotations
# must leave the generated instructions for the same generic field access intact.
sed '/^#\[layout(/d' "$features" > "$work_dir/features.without_layout.sl"
"$compiler" "$work_dir/features.without_layout.sl" --emit.ir --opt.level=none \
	"--tar.triple=$x86_target" --build.output="$work_dir/features.without_layout.ll"
"$llc" -O=0 -filetype=asm "$work_dir/features.without_layout.ll" \
	-o "$work_dir/features.without_layout.s"
"$llc" -O=0 -filetype=asm "$x86_o0" -o "$work_dir/features.layout.s"
if [ "$(asm_instructions "$work_dir/features.layout.s" cell_load)" != \
	"$(asm_instructions "$work_dir/features.without_layout.s" cell_load)" ]; then
	echo "layout assertions changed generated instructions for cell_load" >&2
	exit 1
fi

expect_failure "$fixture_dir/invalid_ranges.sl" invalid_ranges \
	"high bound must be greater than or equal" \
	"outside the integer width" \
	"bound must be a compile-time integer constant" \
	"bound must be nonnegative" \
	"requires an integer operand"
expect_failure "$fixture_dir/invalid_arithmetic.sl" invalid_arithmetic \
	'operator `+%` requires integer operands' \
	"requires operands of the same type"
expect_failure "$fixture_dir/invalid_layout.sl" invalid_layout \
	"E_LAYOUT_MISMATCH" "expected size 12" "target ABI size is 16"
expect_failure "$fixture_dir/invalid_layout_alignment.sl" invalid_layout_alignment \
	"E_LAYOUT_MISMATCH" "expected alignment 4" "target ABI alignment is 8"
expect_failure "$fixture_dir/invalid_layout_arity.sl" invalid_layout_arity \
	"expects exactly two integer arguments: size and alignment"
expect_failure "$fixture_dir/invalid_generic_layout.sl" invalid_generic_layout \
	"E_LAYOUT_MISMATCH" "expected size 8" "target ABI size is 4" \
	"expected alignment 8" "target ABI alignment is 4"
expect_failure "$fixture_dir/invalid_old_integer_types.sl" invalid_old_integer_types \
	'unknown type `ui8`' 'unknown type `si8`' \
	'unknown type `uisize`' 'unknown type `sisize`'
expect_failure "$fixture_dir/invalid_old_generic_constraints.sl" \
	invalid_old_generic_constraints \
	'no matching public function for call to `old_unsigned_constraint`' \
	'no matching public function for call to `old_signed_constraint`'

if "$llc" --version | grep -Eiq '^[[:space:]]*x86[[:space:]]+-'; then
	if "$compiler" "$fixture_dir/invalid_layout_32bit.sl" --build.compile-only \
		--tar.triple=i386-unknown-linux-gnu \
		"--build.output=$work_dir/invalid_layout_32bit.o" \
		>"$work_dir/invalid_layout_32bit.log" 2>&1; then
		echo "expected 32-bit target layout assertion to fail" >&2
		exit 1
	fi
	for diagnostic in "E_LAYOUT_MISMATCH" "expected size 16" "target ABI size is 8" \
		"expected alignment 8" "target ABI alignment is 4"; do
		if ! grep -Fq "$diagnostic" "$work_dir/invalid_layout_32bit.log"; then
			echo "missing target-specific layout diagnostic '$diagnostic'" >&2
			cat "$work_dir/invalid_layout_32bit.log" >&2
			exit 1
		fi
	done
fi

"$compiler" "$features" --build.compile-only --opt.level=none \
	"--tar.triple=$x86_target" "--build.output=$work_dir/features.x86.o"
cat > "$work_dir/runtime.c" <<'EOF'
#include <stdint.h>
#include <limits.h>

extern uint8_t range_extract_runtime(uint32_t);
extern uint8_t range_single_runtime(unsigned __int128);
extern uint8_t range_low_bit_runtime(int16_t);
extern uint8_t array_index(const uint8_t *, uintptr_t);
extern uint8_t wrap_add(uint8_t, uint8_t);
extern uint8_t plain_add(uint8_t, uint8_t);
extern uint8_t wrap_sub(uint8_t, uint8_t);
extern uint8_t wrap_precedence(uint8_t, uint8_t, uint8_t);
extern uint8_t compound_add(uint8_t);
extern int8_t wrap_signed(int8_t, int8_t);
extern int8_t wrap_sub_signed(int8_t, int8_t);
extern uint8_t sat_add_u8(uint8_t, uint8_t);
extern uint8_t sat_sub_u8(uint8_t, uint8_t);
extern int8_t sat_add_s8(int8_t, int8_t);
extern int8_t sat_sub_s8(int8_t, int8_t);
extern uint8_t sat_add_constant(void);
extern uint8_t wrap_add_constant(void);
extern int8_t sat_add_signed_constant(void);
extern int8_t sat_sub_signed_constant(void);
extern intptr_t isize_identity(intptr_t);

int main(void) {
	const uint8_t bytes[] = {3, 7, 11, 19};
	return isize_identity(INTPTR_MIN) != INTPTR_MIN ||
		range_extract_runtime(0xabc) != 21 ||
		range_extract_runtime(UINT32_MAX) != 31 ||
		range_single_runtime(((unsigned __int128)1) << 127) != 1 ||
		range_low_bit_runtime(-3) != 1 || array_index(bytes, 2) != 11 ||
		wrap_add(250, 20) != 14 || plain_add(250, 20) != 14 ||
		wrap_precedence(2, 3, 4) != 14 || wrap_sub(10, 20) != 246 ||
		compound_add(UINT8_MAX) != 0 || wrap_signed(INT8_MAX, 1) != INT8_MIN ||
		wrap_sub_signed(INT8_MIN, 1) != INT8_MAX ||
		sat_add_u8(250, 20) != UINT8_MAX || sat_sub_u8(10, 20) != 0 ||
		sat_add_s8(100, 100) != INT8_MAX || sat_add_s8(-100, -100) != INT8_MIN ||
		sat_sub_s8(-120, 20) != INT8_MIN || sat_sub_s8(120, -20) != INT8_MAX ||
		sat_add_constant() != UINT8_MAX || wrap_add_constant() != 14 ||
		sat_add_signed_constant() != INT8_MAX ||
		sat_sub_signed_constant() != INT8_MIN;
}
EOF
"$c_compiler" "$work_dir/runtime.c" "$work_dir/features.x86.o" \
	-o "$work_dir/language_features_runtime"
"$work_dir/language_features_runtime"

"$compiler" "$fixture_dir/ufcs.sl" --build.compile-only --opt.level=none \
	"--tar.triple=$x86_target" "--build.output=$work_dir/ufcs.x86.o"
cat > "$work_dir/ufcs_runtime.c" <<'EOF'
#include <stdint.h>

struct Point {
	int32_t x;
	int32_t y;
};

extern int32_t test_ufcs_chain(int32_t);
extern int32_t test_direct_chain(int32_t);
extern int32_t test_builder_chain(void);
extern int32_t test_auto_ref(void);
extern int32_t test_auto_ref_mut(void);
extern int32_t test_auto_deref(const struct Point *);
extern float test_struct_scoped_ufcs(void);
extern int32_t test_mod_and_generic_impl(int32_t);
extern int32_t test_generic_ufcs(int32_t);
extern int32_t test_primitive_ufcs(int32_t);
extern int32_t test_priority1_fn_ptr(void);
extern int32_t test_ufcs_point_call(void);

int main(void) {
	struct Point p = {3, 4};
	return test_ufcs_chain(10) != 26 ||
		test_direct_chain(10) != 26 ||
		test_builder_chain() != 200 ||
		test_auto_ref() != 30 ||
		test_auto_ref_mut() != 14 ||
		test_auto_deref(&p) != 25 ||
		test_struct_scoped_ufcs() != 4.0f ||
		test_mod_and_generic_impl(21) != 42 ||
		test_generic_ufcs(42) != 42 ||
		test_primitive_ufcs(-42) != 42 ||
		test_priority1_fn_ptr() != 42 ||
		test_ufcs_point_call() != 25;
}
EOF
"$c_compiler" "$work_dir/ufcs_runtime.c" "$work_dir/ufcs.x86.o" \
	-o "$work_dir/ufcs_runtime"
"$work_dir/ufcs_runtime"

"$compiler" "$fixture_dir/traits.sl" --build.compile-only --opt.level=none \
	"--tar.triple=$x86_target" "--build.output=$work_dir/traits.x86.o"
cat > "$work_dir/traits_runtime.c" <<'EOF'
#include <stdint.h>

extern int32_t test_trait_basic(void);
extern int32_t test_trait_generic(void);
extern int32_t test_trait_multiple_bounds(void);
extern int32_t test_trait_primitive(void);
extern int32_t test_trait_generic_impl(void);

int main(void) {
	return test_trait_basic() != 30 ||
		test_trait_generic() != 20 ||
		test_trait_multiple_bounds() != 30 ||
		test_trait_primitive() != 70 ||
		test_trait_generic_impl() != 260;
}
EOF
"$c_compiler" "$work_dir/traits_runtime.c" "$work_dir/traits.x86.o" \
	-o "$work_dir/traits_runtime"
"$work_dir/traits_runtime"

"$compiler" "$fixture_dir/stdlib_traits.sl" --build.compile-only --opt.level=none \
	"--tar.triple=$x86_target" "--build.output=$work_dir/stdlib_traits.x86.o"
cat > "$work_dir/stdlib_traits_runtime.c" <<'EOF'
#include <stdint.h>

extern int32_t test_stream_copy(void);
extern int32_t test_ord_sort(void);
extern int32_t test_disposable(void);

int main(void) {
	return test_stream_copy() != 42 ||
		test_ord_sort() != 100 ||
		test_disposable() != 200;
}
EOF
"$c_compiler" "$work_dir/stdlib_traits_runtime.c" "$work_dir/stdlib_traits.x86.o" \
	-o "$work_dir/stdlib_traits_runtime"
"$work_dir/stdlib_traits_runtime"