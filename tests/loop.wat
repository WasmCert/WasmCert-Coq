(module
	(func (export "loop_br")
		(loop
			br 1))
	(func (export "block_br")
		(block
			br 0))
	(func (export "br")
		br 0)
)
