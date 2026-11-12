import "private_a.sl";
import "unrelated.sl";
import "private_b.sl";

#[export]
pub fn optimized_multi_extra() i32 {
	return private_a_value() + private_b_value();
}