(module
	(func (export "main")
		(loop
			br 1))
	(func (export "block_br")
		(block
			br 0))
	(func (export "br")
		br 0)
)
