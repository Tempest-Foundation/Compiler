#[layout(16, 8)]
struct Header {
	magic: u32,
	flags: u32,
	address: u64,
}

#[layout(4, 4)]
struct SizeAndAlignment {
	value: u32,
}

#[layout(16, 8)]
struct PointerHeader {
	value: *u8,
	tag: u8,
}

#[layout(8, 8)]
struct Cell<T> {
	value: T,
}

#[export("isize_identity")]
pub fn isize_identity(value: isize) isize {
	return value;
}

#[export("range_extract")]
pub fn range_extract(x: u32) u5 {
	return x[11:7];
}

#[export("range_extract_runtime")]
pub fn range_extract_runtime(x: u32) u8 {
	return x[11:7] cast u8;
}

#[export("range_extract_manual")]
pub fn range_extract_manual(x: u32) u5 {
	return (x >> 7) cast u5;
}

#[export("range_single")]
pub fn range_single(x: u128) u1 {
	return x[127:127];
}

#[export("range_single_runtime")]
pub fn range_single_runtime(x: u128) u8 {
	return x[127:127] cast u8;
}

#[export("range_low_bit")]
pub fn range_low_bit(x: i16) u1 {
	return x[0:0];
}

#[export("range_low_bit_runtime")]
pub fn range_low_bit_runtime(x: i16) u8 {
	return x[0:0] cast u8;
}

#[export("range_wide")]
pub fn range_wide(x: u129) u65 {
	return x[100:36];
}

#[export("array_index")]
pub fn array_index(x: *u8, idx: usize) u8 {
	return x[idx];
}

#[export("wrap_add")]
pub fn wrap_add(x: u8, y: u8) u8 {
	return x +% y;
}

#[export("plain_add")]
pub fn plain_add(x: u8, y: u8) u8 {
	return x + y;
}

#[export("wrap_precedence")]
pub fn wrap_precedence(x: u8, y: u8, z: u8) u8 {
	return x +% y * z;
}

#[export("plain_precedence")]
pub fn plain_precedence(x: u8, y: u8, z: u8) u8 {
	return x + y * z;
}

#[export("wrap_sub")]
pub fn wrap_sub(x: u8, y: u8) u8 {
	return x -% y;
}

#[export("wrap_sub_signed")]
pub fn wrap_sub_signed(x: i8, y: i8) i8 {
	return x -% y;
}

#[export("plain_sub")]
pub fn plain_sub(x: u8, y: u8) u8 {
	return x - y;
}

#[export("compound_add")]
pub fn compound_add(x: u8) u8 {
	let mut value: u8 = x;
	value += 1;
	return value;
}

#[export("wrap_signed")]
pub fn wrap_signed(x: i8, y: i8) i8 {
	return x +% y;
}

#[export("wrap_add_u129")]
pub fn wrap_add_u129(x: u129, y: u129) u129 {
	return x +% y;
}

#[export("sat_add_u8")]
pub fn sat_add_u8(x: u8, y: u8) u8 {
	return x +| y;
}

#[export("sat_sub_u8")]
pub fn sat_sub_u8(x: u8, y: u8) u8 {
	return x -| y;
}

#[export("sat_add_s8")]
pub fn sat_add_s8(x: i8, y: i8) i8 {
	return x +| y;
}

#[export("sat_sub_s8")]
pub fn sat_sub_s8(x: i8, y: i8) i8 {
	return x -| y;
}

#[export("sat_add_u129")]
pub fn sat_add_u129(x: u129, y: u129) u129 {
	return x +| y;
}

#[export("sat_sub_u129")]
pub fn sat_sub_u129(x: u129, y: u129) u129 {
	return x -| y;
}

#[export("sat_add_s129")]
pub fn sat_add_s129(x: i129, y: i129) i129 {
	return x +| y;
}

#[export("sat_sub_s129")]
pub fn sat_sub_s129(x: i129, y: i129) i129 {
	return x -| y;
}

#[export("sat_add_u129_constant")]
pub fn sat_add_u129_constant() u129 {
	return ((((1 cast u129) << 128) - 1) + ((1 cast u129) << 128)) +| 1;
}

#[export("wrap_add_u129_constant")]
pub fn wrap_add_u129_constant() u129 {
	return ((1 cast u129) << 128) +% ((1 cast u129) << 128);
}

#[export("sat_add_constant")]
pub fn sat_add_constant() u8 {
	return 250 +| 20;
}

#[export("wrap_add_constant")]
pub fn wrap_add_constant() u8 {
	return 250 +% 20;
}

#[export("sat_add_signed_constant")]
pub fn sat_add_signed_constant() i8 {
	return 120 +| 20;
}

#[export("sat_sub_signed_constant")]
pub fn sat_sub_signed_constant() i8 {
	return -120 -| 20;
}

#[export("cell_load")]
pub fn cell_load(x: *Cell<u64>) u64 {
	return x.value;
}

#[export("gcd_mut")]
pub fn gcd_mut(mut a: u64, mut b: u64) u64 {
	for b != 0 {
		let t: u64 = b;
		b = a % b;
		a = t;
	}
	return a;
}