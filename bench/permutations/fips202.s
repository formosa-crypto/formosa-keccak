	.file	"fips202.c"
	.text
	.globl	KeccakF1600_StatePermute        # -- Begin function KeccakF1600_StatePermute
	.p2align	4
	.type	KeccakF1600_StatePermute,@function
KeccakF1600_StatePermute:               # @KeccakF1600_StatePermute
	.cfi_startproc
# %bb.0:
	pushq	%rbp
	.cfi_def_cfa_offset 16
	pushq	%r15
	.cfi_def_cfa_offset 24
	pushq	%r14
	.cfi_def_cfa_offset 32
	pushq	%r13
	.cfi_def_cfa_offset 40
	pushq	%r12
	.cfi_def_cfa_offset 48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	subq	$96, %rsp
	.cfi_def_cfa_offset 152
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rdi, %rcx
	movq	(%rdi), %rbp
	movq	8(%rdi), %rax
	movq	%rax, -16(%rsp)                 # 8-byte Spill
	movq	16(%rdi), %rax
	movq	%rax, 8(%rsp)                   # 8-byte Spill
	movq	24(%rdi), %rax
	movq	%rax, -40(%rsp)                 # 8-byte Spill
	movq	32(%rdi), %rax
	movq	%rax, -8(%rsp)                  # 8-byte Spill
	movq	40(%rdi), %rax
	movq	%rax, -48(%rsp)                 # 8-byte Spill
	movq	48(%rdi), %rax
	movq	%rax, -88(%rsp)                 # 8-byte Spill
	movq	56(%rdi), %rax
	movq	%rax, -96(%rsp)                 # 8-byte Spill
	movq	64(%rdi), %rax
	movq	%rax, (%rsp)                    # 8-byte Spill
	movq	72(%rdi), %rax
	movq	%rax, -120(%rsp)                # 8-byte Spill
	movq	80(%rdi), %rdi
	movq	88(%rcx), %rax
	movq	%rax, -64(%rsp)                 # 8-byte Spill
	movq	96(%rcx), %r13
	movq	104(%rcx), %rax
	movq	%rax, -104(%rsp)                # 8-byte Spill
	movq	112(%rcx), %rax
	movq	%rax, -56(%rsp)                 # 8-byte Spill
	movq	120(%rcx), %rax
	movq	%rax, -72(%rsp)                 # 8-byte Spill
	movq	128(%rcx), %rax
	movq	%rax, -128(%rsp)                # 8-byte Spill
	movq	136(%rcx), %rax
	movq	%rax, -112(%rsp)                # 8-byte Spill
	movq	144(%rcx), %r10
	movq	152(%rcx), %r11
	movq	160(%rcx), %r8
	movq	168(%rcx), %rsi
	movq	176(%rcx), %r15
	movq	184(%rcx), %rax
	movq	%rax, -80(%rsp)                 # 8-byte Spill
	movq	%rcx, 72(%rsp)                  # 8-byte Spill
	movq	192(%rcx), %rbx
	movq	$-2, %rax
	.p2align	4
.LBB0_1:                                # =>This Inner Loop Header: Depth=1
	movq	%r11, -32(%rsp)                 # 8-byte Spill
	movq	%rdi, -24(%rsp)                 # 8-byte Spill
	movq	%rax, 24(%rsp)                  # 8-byte Spill
	movq	%rsi, 16(%rsp)                  # 8-byte Spill
	movq	-72(%rsp), %rcx                 # 8-byte Reload
	xorq	%r8, %rcx
	movq	%rdi, %rax
	xorq	-48(%rsp), %rax                 # 8-byte Folded Reload
	xorq	%rcx, %rax
	movq	-128(%rsp), %rdx                # 8-byte Reload
	xorq	%rsi, %rdx
	movq	-64(%rsp), %rcx                 # 8-byte Reload
	movq	-88(%rsp), %rsi                 # 8-byte Reload
	xorq	%rsi, %rcx
	xorq	%rdx, %rcx
	movq	-112(%rsp), %rdx                # 8-byte Reload
	xorq	%r15, %rdx
	movq	%r13, %r9
	xorq	-96(%rsp), %r9                  # 8-byte Folded Reload
	xorq	%rdx, %r9
	movq	%r10, %rdx
	xorq	-80(%rsp), %rdx                 # 8-byte Folded Reload
	movq	-104(%rsp), %r12                # 8-byte Reload
	xorq	(%rsp), %r12                    # 8-byte Folded Reload
	xorq	%rdx, %r12
	movq	%r11, %rdx
	xorq	%rbx, %rdx
	movq	-56(%rsp), %r14                 # 8-byte Reload
	xorq	-120(%rsp), %r14                # 8-byte Folded Reload
	xorq	%rdx, %r14
	xorq	%rbp, %rax
	xorq	-16(%rsp), %rcx                 # 8-byte Folded Reload
	xorq	8(%rsp), %r9                    # 8-byte Folded Reload
	movq	-40(%rsp), %rdi                 # 8-byte Reload
	xorq	%rdi, %r12
	xorq	-8(%rsp), %r14                  # 8-byte Folded Reload
	rorxq	$63, %r12, %rdx
	xorq	%rcx, %rdx
	movq	%rdx, 88(%rsp)                  # 8-byte Spill
	rorxq	$63, %rcx, %r11
	xorq	%r14, %r11
	movq	%r11, 80(%rsp)                  # 8-byte Spill
	rorxq	$63, %r14, %rcx
	xorq	%r9, %rcx
	rorxq	$63, %r9, %r9
	xorq	%rax, %r9
	rorxq	$63, %rax, %rax
	xorq	%r12, %rax
	xorq	%r11, %rbp
	xorq	%r9, %rsi
	movq	%r9, %r11
	rorxq	$20, %rsi, %r9
	xorq	%rdx, %r13
	rorxq	$21, %r13, %r14
	xorq	%rcx, %r10
	rorxq	$43, %r10, %r10
	xorq	%rax, %rbx
	rorxq	$50, %rbx, %rbx
	andnq	%rbp, %rbx, %rsi
	xorq	%r10, %rsi
	movq	%rsi, -88(%rsp)                 # 8-byte Spill
	andnq	%r10, %r14, %rsi
	andnq	%rbx, %r10, %r10
	xorq	%r14, %r10
	movq	%r10, 64(%rsp)                  # 8-byte Spill
	andnq	%r14, %r9, %r12
	leaq	KeccakF_RoundConstants(%rip), %r10
	movq	24(%rsp), %r14                  # 8-byte Reload
	xorq	16(%r10,%r14,8), %r12
	xorq	%rbp, %r12
	xorq	%r9, %rsi
	movq	%rsi, 48(%rsp)                  # 8-byte Spill
	andnq	%r9, %rbp, %r9
	xorq	%rbx, %r9
	movq	%r9, 56(%rsp)                   # 8-byte Spill
	xorq	%rcx, %rdi
	movq	%rcx, %rdx
	rorxq	$36, %rdi, %r9
	movq	-120(%rsp), %rsi                # 8-byte Reload
	xorq	%rax, %rsi
	rorxq	$44, %rsi, %r10
	movq	-24(%rsp), %rsi                 # 8-byte Reload
	movq	80(%rsp), %r13                  # 8-byte Reload
	xorq	%r13, %rsi
	rorxq	$61, %rsi, %rsi
	movq	-128(%rsp), %rdi                # 8-byte Reload
	movq	%r11, %rcx
	xorq	%r11, %rdi
	rorxq	$19, %rdi, %rdi
	movq	88(%rsp), %rbp                  # 8-byte Reload
	xorq	%rbp, %r15
	rorxq	$3, %r15, %rbx
	andnq	%r9, %rbx, %r15
	xorq	%rdi, %r15
	movq	%r15, -24(%rsp)                 # 8-byte Spill
	andnq	%rdi, %rsi, %r15
	andnq	%rbx, %rdi, %rdi
	xorq	%rsi, %rdi
	movq	%rdi, 40(%rsp)                  # 8-byte Spill
	andnq	%rsi, %r10, %rsi
	xorq	%r9, %rsi
	movq	%rsi, -128(%rsp)                # 8-byte Spill
	xorq	%r10, %r15
	movq	%r15, -40(%rsp)                 # 8-byte Spill
	andnq	%r10, %r9, %rsi
	xorq	%rbx, %rsi
	movq	%rsi, -120(%rsp)                # 8-byte Spill
	movq	-16(%rsp), %rsi                 # 8-byte Reload
	xorq	%r11, %rsi
	rorxq	$63, %rsi, %rsi
	movq	-96(%rsp), %rdi                 # 8-byte Reload
	xorq	%rbp, %rdi
	rorxq	$58, %rdi, %rdi
	movq	-104(%rsp), %r9                 # 8-byte Reload
	xorq	%rdx, %r9
	rorxq	$39, %r9, %r9
	movq	-32(%rsp), %r10                 # 8-byte Reload
	xorq	%rax, %r10
	rorxq	$56, %r10, %r10
	movq	%r13, %r14
	xorq	%r13, %r8
	rorxq	$46, %r8, %r8
	andnq	%rsi, %r8, %r11
	xorq	%r10, %r11
	movq	%r11, -104(%rsp)                # 8-byte Spill
	andnq	%r10, %r9, %r11
	andnq	%r8, %r10, %r13
	xorq	%r9, %r13
	andnq	%r9, %rdi, %r9
	xorq	%rsi, %r9
	movq	%r9, -96(%rsp)                  # 8-byte Spill
	xorq	%rdi, %r11
	movq	%r11, 32(%rsp)                  # 8-byte Spill
	andnq	%rdi, %rsi, %rsi
	xorq	%r8, %rsi
	movq	%rsi, -32(%rsp)                 # 8-byte Spill
	movq	-8(%rsp), %rsi                  # 8-byte Reload
	xorq	%rax, %rsi
	rorxq	$37, %rsi, %rsi
	movq	-48(%rsp), %rdi                 # 8-byte Reload
	xorq	%r14, %rdi
	rorxq	$28, %rdi, %rdi
	movq	-64(%rsp), %r8                  # 8-byte Reload
	xorq	%rcx, %r8
	rorxq	$54, %r8, %r8
	movq	-112(%rsp), %r9                 # 8-byte Reload
	xorq	%rbp, %r9
	rorxq	$49, %r9, %r11
	movq	-80(%rsp), %r9                  # 8-byte Reload
	xorq	%rdx, %r9
	rorxq	$8, %r9, %rbx
	andnq	%rsi, %rbx, %r10
	xorq	%r11, %r10
	andnq	%r11, %r8, %r15
	andnq	%rbx, %r11, %r11
	xorq	%r8, %r11
	movq	%r11, -112(%rsp)                # 8-byte Spill
	andnq	%r8, %rdi, %r8
	xorq	%rsi, %r8
	movq	%r8, -80(%rsp)                  # 8-byte Spill
	xorq	%rdi, %r15
	movq	%r15, -48(%rsp)                 # 8-byte Spill
	andnq	%rdi, %rsi, %rsi
	xorq	%rbx, %rsi
	movq	%rsi, -64(%rsp)                 # 8-byte Spill
	movq	%rbp, %rsi
	xorq	8(%rsp), %rsi                   # 8-byte Folded Reload
	xorq	(%rsp), %rdx                    # 8-byte Folded Reload
	xorq	-56(%rsp), %rax                 # 8-byte Folded Reload
	movq	%r14, %rdi
	xorq	-72(%rsp), %rdi                 # 8-byte Folded Reload
	xorq	16(%rsp), %rcx                  # 8-byte Folded Reload
	rorxq	$2, %rsi, %rsi
	rorxq	$9, %rdx, %rdx
	rorxq	$25, %rax, %rax
	rorxq	$23, %rdi, %rdi
	rorxq	$62, %rcx, %rcx
	andnq	%rsi, %rcx, %r9
	xorq	%rdi, %r9
	movq	%r9, -72(%rsp)                  # 8-byte Spill
	andnq	%rdi, %rax, %r14
	andnq	%rcx, %rdi, %r11
	xorq	%rax, %r11
	andnq	%rax, %rdx, %rax
	xorq	%rsi, %rax
	movq	%rax, %rbp
	movq	%rax, -56(%rsp)                 # 8-byte Spill
	xorq	%rdx, %r14
	movq	%r14, 16(%rsp)                  # 8-byte Spill
	andnq	%rdx, %rsi, %rdi
	xorq	%rcx, %rdi
	movq	%r8, %rax
	xorq	-96(%rsp), %rax                 # 8-byte Folded Reload
	movq	-128(%rsp), %rsi                # 8-byte Reload
	xorq	%rbp, %rsi
	xorq	%rax, %rsi
	movq	-40(%rsp), %rbp                 # 8-byte Reload
	movq	%rbp, %rax
	xorq	48(%rsp), %rax                  # 8-byte Folded Reload
	movq	%r15, %rdx
	xorq	32(%rsp), %rdx                  # 8-byte Folded Reload
	xorq	%rax, %rdx
	movq	40(%rsp), %rax                  # 8-byte Reload
	xorq	-112(%rsp), %rax                # 8-byte Folded Reload
	movq	%r11, %r8
	xorq	64(%rsp), %r8                   # 8-byte Folded Reload
	xorq	%rax, %r8
	movq	-104(%rsp), %rbx                # 8-byte Reload
	xorq	-24(%rsp), %rbx                 # 8-byte Folded Reload
	movq	%r9, %rcx
	xorq	-88(%rsp), %rcx                 # 8-byte Folded Reload
	xorq	%rbx, %rcx
	movq	56(%rsp), %rbx                  # 8-byte Reload
	xorq	%rdi, %rbx
	movq	-32(%rsp), %rax                 # 8-byte Reload
	xorq	-120(%rsp), %rax                # 8-byte Folded Reload
	xorq	%rbx, %rax
	xorq	%r12, %rsi
	xorq	%r14, %rdx
	xorq	%r13, %r8
	xorq	%r10, %rcx
	movq	-64(%rsp), %r14                 # 8-byte Reload
	xorq	%r14, %rax
	rorxq	$63, %rcx, %r15
	xorq	%rdx, %r15
	rorxq	$63, %rdx, %rbx
	xorq	%rax, %rbx
	rorxq	$63, %rax, %r9
	xorq	%r8, %r9
	rorxq	$63, %r8, %r8
	xorq	%rsi, %r8
	rorxq	$63, %rsi, %rdx
	xorq	%rcx, %rdx
	xorq	%rbx, %r12
	xorq	%r8, %rbp
	rorxq	$20, %rbp, %rax
	xorq	%r15, %r13
	rorxq	$21, %r13, %rcx
	xorq	%r9, %r10
	rorxq	$43, %r10, %rsi
	xorq	%rdx, %rdi
	rorxq	$50, %rdi, %rdi
	andnq	%r12, %rdi, %r10
	xorq	%rsi, %r10
	movq	%r10, -40(%rsp)                 # 8-byte Spill
	andnq	%rsi, %rcx, %r10
	andnq	%rdi, %rsi, %rsi
	xorq	%rcx, %rsi
	movq	%rsi, 8(%rsp)                   # 8-byte Spill
	andnq	%rcx, %rax, %rbp
	movq	24(%rsp), %rcx                  # 8-byte Reload
	leaq	KeccakF_RoundConstants(%rip), %rsi
	xorq	24(%rsi,%rcx,8), %rbp
	xorq	%r12, %rbp
	xorq	%rax, %r10
	movq	%r10, -16(%rsp)                 # 8-byte Spill
	andnq	%rax, %r12, %rax
	xorq	%rdi, %rax
	movq	%rax, -8(%rsp)                  # 8-byte Spill
	movq	-88(%rsp), %rax                 # 8-byte Reload
	xorq	%r9, %rax
	rorxq	$36, %rax, %rax
	movq	-120(%rsp), %rcx                # 8-byte Reload
	xorq	%rdx, %rcx
	rorxq	$44, %rcx, %rcx
	movq	-96(%rsp), %rsi                 # 8-byte Reload
	xorq	%rbx, %rsi
	rorxq	$61, %rsi, %rsi
	movq	-48(%rsp), %rdi                 # 8-byte Reload
	xorq	%r8, %rdi
	rorxq	$19, %rdi, %rdi
	xorq	%r15, %r11
	rorxq	$3, %r11, %r10
	andnq	%rax, %r10, %r11
	xorq	%rdi, %r11
	movq	%r11, (%rsp)                    # 8-byte Spill
	andnq	%rdi, %rsi, %r11
	andnq	%r10, %rdi, %rdi
	xorq	%rsi, %rdi
	movq	%rdi, -96(%rsp)                 # 8-byte Spill
	andnq	%rsi, %rcx, %rsi
	xorq	%rax, %rsi
	movq	%rsi, -48(%rsp)                 # 8-byte Spill
	xorq	%rcx, %r11
	movq	%r11, -88(%rsp)                 # 8-byte Spill
	andnq	%rcx, %rax, %rax
	xorq	%r10, %rax
	movq	%rax, -120(%rsp)                # 8-byte Spill
	movq	48(%rsp), %rax                  # 8-byte Reload
	xorq	%r8, %rax
	rorxq	$63, %rax, %rax
	movq	40(%rsp), %rcx                  # 8-byte Reload
	xorq	%r15, %rcx
	rorxq	$58, %rcx, %rcx
	movq	-104(%rsp), %rsi                # 8-byte Reload
	xorq	%r9, %rsi
	rorxq	$39, %rsi, %rsi
	movq	%r14, %rdi
	xorq	%rdx, %rdi
	rorxq	$56, %rdi, %rdi
	movq	-56(%rsp), %r10                 # 8-byte Reload
	xorq	%rbx, %r10
	rorxq	$46, %r10, %r10
	andnq	%rax, %r10, %r11
	xorq	%rdi, %r11
	movq	%r11, -104(%rsp)                # 8-byte Spill
	andnq	%rdi, %rsi, %r11
	andnq	%r10, %rdi, %r13
	xorq	%rsi, %r13
	andnq	%rsi, %rcx, %rdi
	xorq	%rax, %rdi
	xorq	%rcx, %r11
	movq	%r11, -64(%rsp)                 # 8-byte Spill
	andnq	%rcx, %rax, %rax
	xorq	%r10, %rax
	movq	%rax, -56(%rsp)                 # 8-byte Spill
	movq	56(%rsp), %rax                  # 8-byte Reload
	xorq	%rdx, %rax
	rorxq	$37, %rax, %rax
	movq	-128(%rsp), %rcx                # 8-byte Reload
	xorq	%rbx, %rcx
	rorxq	$28, %rcx, %rcx
	movq	32(%rsp), %rsi                  # 8-byte Reload
	xorq	%r8, %rsi
	rorxq	$54, %rsi, %r11
	movq	-112(%rsp), %rsi                # 8-byte Reload
	xorq	%r15, %rsi
	rorxq	$49, %rsi, %r14
	movq	-72(%rsp), %rsi                 # 8-byte Reload
	xorq	%r9, %rsi
	rorxq	$8, %rsi, %r12
	andnq	%rax, %r12, %r10
	xorq	%r14, %r10
	andnq	%r14, %r11, %rsi
	andnq	%r12, %r14, %r14
	xorq	%r11, %r14
	movq	%r14, -112(%rsp)                # 8-byte Spill
	andnq	%r11, %rcx, %r11
	xorq	%rax, %r11
	movq	%r11, -72(%rsp)                 # 8-byte Spill
	xorq	%rcx, %rsi
	movq	%rsi, -128(%rsp)                # 8-byte Spill
	andnq	%rcx, %rax, %r11
	xorq	%r12, %r11
	xorq	64(%rsp), %r15                  # 8-byte Folded Reload
	xorq	-24(%rsp), %r9                  # 8-byte Folded Reload
	xorq	-32(%rsp), %rdx                 # 8-byte Folded Reload
	xorq	-80(%rsp), %rbx                 # 8-byte Folded Reload
	xorq	16(%rsp), %r8                   # 8-byte Folded Reload
	rorxq	$2, %r15, %rax
	rorxq	$9, %r9, %rcx
	rorxq	$25, %rdx, %rdx
	rorxq	$23, %rbx, %r9
	rorxq	$62, %r8, %r14
	andnq	%rax, %r14, %r8
	xorq	%r9, %r8
	movq	%r8, -80(%rsp)                  # 8-byte Spill
	andnq	%r9, %rdx, %rsi
	andnq	%r14, %r9, %r15
	xorq	%rdx, %r15
	andnq	%rdx, %rcx, %r8
	xorq	%rax, %r8
	xorq	%rcx, %rsi
	andnq	%rcx, %rax, %rbx
	xorq	%r14, %rbx
	movq	24(%rsp), %rcx                  # 8-byte Reload
	addq	$2, %rcx
	movq	%rcx, %rax
	cmpq	$22, %rcx
	jb	.LBB0_1
# %bb.2:
	movq	72(%rsp), %rax                  # 8-byte Reload
	movq	%rbp, (%rax)
	movq	-16(%rsp), %rcx                 # 8-byte Reload
	movq	%rcx, 8(%rax)
	movq	8(%rsp), %rcx                   # 8-byte Reload
	movq	%rcx, 16(%rax)
	movq	-40(%rsp), %rcx                 # 8-byte Reload
	movq	%rcx, 24(%rax)
	movq	-8(%rsp), %rcx                  # 8-byte Reload
	movq	%rcx, 32(%rax)
	movq	-48(%rsp), %rcx                 # 8-byte Reload
	movq	%rcx, 40(%rax)
	movq	-88(%rsp), %rcx                 # 8-byte Reload
	movq	%rcx, 48(%rax)
	movq	-96(%rsp), %rcx                 # 8-byte Reload
	movq	%rcx, 56(%rax)
	movq	(%rsp), %rcx                    # 8-byte Reload
	movq	%rcx, 64(%rax)
	movq	-120(%rsp), %rcx                # 8-byte Reload
	movq	%rcx, 72(%rax)
	movq	%rdi, 80(%rax)
	movq	-64(%rsp), %rcx                 # 8-byte Reload
	movq	%rcx, 88(%rax)
	movq	%r13, 96(%rax)
	movq	-104(%rsp), %rcx                # 8-byte Reload
	movq	%rcx, 104(%rax)
	movq	-56(%rsp), %rcx                 # 8-byte Reload
	movq	%rcx, 112(%rax)
	movq	-72(%rsp), %rcx                 # 8-byte Reload
	movq	%rcx, 120(%rax)
	movq	-128(%rsp), %rcx                # 8-byte Reload
	movq	%rcx, 128(%rax)
	movq	-112(%rsp), %rcx                # 8-byte Reload
	movq	%rcx, 136(%rax)
	movq	%r10, 144(%rax)
	movq	%r11, 152(%rax)
	movq	%r8, 160(%rax)
	movq	%rsi, 168(%rax)
	movq	%r15, 176(%rax)
	movq	-80(%rsp), %rcx                 # 8-byte Reload
	movq	%rcx, 184(%rax)
	movq	%rbx, 192(%rax)
	addq	$96, %rsp
	.cfi_def_cfa_offset 56
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%r12
	.cfi_def_cfa_offset 40
	popq	%r13
	.cfi_def_cfa_offset 32
	popq	%r14
	.cfi_def_cfa_offset 24
	popq	%r15
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end0:
	.size	KeccakF1600_StatePermute, .Lfunc_end0-KeccakF1600_StatePermute
	.cfi_endproc
                                        # -- End function
	.globl	shake128_init                   # -- Begin function shake128_init
	.p2align	4
	.type	shake128_init,@function
shake128_init:                          # @shake128_init
	.cfi_startproc
# %bb.0:
	vxorps	%xmm0, %xmm0, %xmm0
	vmovups	%ymm0, 172(%rdi)
	vmovups	%ymm0, 160(%rdi)
	vmovups	%ymm0, 128(%rdi)
	vmovups	%ymm0, 96(%rdi)
	vmovups	%ymm0, 64(%rdi)
	vmovups	%ymm0, 32(%rdi)
	vmovups	%ymm0, (%rdi)
	vzeroupper
	retq
.Lfunc_end1:
	.size	shake128_init, .Lfunc_end1-shake128_init
	.cfi_endproc
                                        # -- End function
	.globl	shake128_absorb                 # -- Begin function shake128_absorb
	.p2align	4
	.type	shake128_absorb,@function
shake128_absorb:                        # @shake128_absorb
	.cfi_startproc
# %bb.0:
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%rbx
	.cfi_def_cfa_offset 32
	.cfi_offset %rbx, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%rsi, %r14
	movq	%rdi, %rbx
	movl	200(%rdi), %eax
	movq	%rax, %rcx
	addq	%rdx, %rcx
	cmpq	$168, %rcx
	jae	.LBB2_6
# %bb.1:
	movq	%rcx, %r15
.LBB2_2:
	movl	%eax, %ecx
	cmpq	%rcx, %r15
	jbe	.LBB2_5
# %bb.3:
	leal	(,%rax,8), %ecx
	.p2align	4
.LBB2_4:                                # =>This Inner Loop Header: Depth=1
	movzbl	(%r14), %edx
	movl	%ecx, %esi
	andb	$56, %sil
	shlxq	%rsi, %rdx, %rdx
	movl	%eax, %esi
	andl	$-8, %esi
	xorq	%rdx, (%rbx,%rsi)
	incq	%r14
	incl	%eax
	addl	$8, %ecx
	cmpq	%rax, %r15
	ja	.LBB2_4
.LBB2_5:
	movl	%eax, 200(%rbx)
	popq	%rbx
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	retq
.LBB2_6:
	.cfi_def_cfa_offset 32
	movq	%rdx, %r15
	jmp	.LBB2_7
	.p2align	4
.LBB2_16:                               #   in Loop: Header=BB2_7 Depth=1
	movl	$168, %ecx
	subl	%eax, %ecx
	subq	%rcx, %r15
	movq	%rbx, %rdi
	callq	KeccakF1600_StatePermute
	xorl	%eax, %eax
	cmpq	$168, %r15
	jb	.LBB2_2
.LBB2_7:                                # =>This Loop Header: Depth=1
                                        #     Child Loop BB2_11 Depth 2
                                        #     Child Loop BB2_14 Depth 2
	cmpl	$167, %eax
	ja	.LBB2_16
# %bb.8:                                #   in Loop: Header=BB2_7 Depth=1
	movl	%eax, %edx
	negl	%edx
	andl	$3, %edx
	je	.LBB2_9
# %bb.10:                               #   in Loop: Header=BB2_7 Depth=1
	leal	(,%rax,8), %esi
	movl	%eax, %ecx
	.p2align	4
.LBB2_11:                               #   Parent Loop BB2_7 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	movzbl	(%r14), %edi
	movl	%esi, %r8d
	andb	$56, %r8b
	shlxq	%r8, %rdi, %rdi
	movl	%ecx, %r8d
	andl	$-8, %r8d
	xorq	%rdi, (%rbx,%r8)
	incq	%r14
	incl	%ecx
	addl	$8, %esi
	decl	%edx
	jne	.LBB2_11
# %bb.12:                               #   in Loop: Header=BB2_7 Depth=1
	cmpl	$164, %eax
	jbe	.LBB2_13
	jmp	.LBB2_16
	.p2align	4
.LBB2_9:                                #   in Loop: Header=BB2_7 Depth=1
	movl	%eax, %ecx
	cmpl	$164, %eax
	ja	.LBB2_16
.LBB2_13:                               #   in Loop: Header=BB2_7 Depth=1
	movl	%ecx, %edx
	shll	$3, %ecx
	xorl	%esi, %esi
	.p2align	4
.LBB2_14:                               #   Parent Loop BB2_7 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	leal	(%rdx,%rsi), %edi
	movzbl	(%r14,%rsi), %r8d
	movl	%ecx, %r9d
	andb	$56, %r9b
	shlxq	%r9, %r8, %r8
	andl	$-8, %edi
	xorq	%r8, (%rbx,%rdi)
	leal	(%rdx,%rsi), %edi
	incl	%edi
	movzbl	1(%r14,%rsi), %r8d
	leal	8(%rcx), %r9d
	andb	$56, %r9b
	shlxq	%r9, %r8, %r8
	andl	$-8, %edi
	xorq	%r8, (%rbx,%rdi)
	leal	(%rdx,%rsi), %edi
	addl	$2, %edi
	movzbl	2(%r14,%rsi), %r8d
	leal	16(%rcx), %r9d
	andb	$56, %r9b
	shlxq	%r9, %r8, %r8
	andl	$-8, %edi
	xorq	%r8, (%rbx,%rdi)
	leal	(%rdx,%rsi), %edi
	addl	$3, %edi
	movzbl	3(%r14,%rsi), %r8d
	leal	24(%rcx), %r9d
	andb	$56, %r9b
	shlxq	%r9, %r8, %r8
	andl	$-8, %edi
	xorq	%r8, (%rbx,%rdi)
	addq	$4, %rsi
	leal	(%rsi,%rdx), %edi
	addl	$32, %ecx
	cmpl	$168, %edi
	jne	.LBB2_14
# %bb.15:                               #   in Loop: Header=BB2_7 Depth=1
	addq	%rsi, %r14
	jmp	.LBB2_16
.Lfunc_end2:
	.size	shake128_absorb, .Lfunc_end2-shake128_absorb
	.cfi_endproc
                                        # -- End function
	.globl	shake128_finalize               # -- Begin function shake128_finalize
	.p2align	4
	.type	shake128_finalize,@function
shake128_finalize:                      # @shake128_finalize
	.cfi_startproc
# %bb.0:
	movl	200(%rdi), %eax
	leal	(,%rax,8), %ecx
	movl	$31, %edx
	shlxq	%rcx, %rdx, %rcx
	andl	$-8, %eax
	xorq	%rcx, (%rdi,%rax)
	xorb	$-128, 167(%rdi)
	movl	$168, 200(%rdi)
	retq
.Lfunc_end3:
	.size	shake128_finalize, .Lfunc_end3-shake128_finalize
	.cfi_endproc
                                        # -- End function
	.globl	shake128_squeeze                # -- Begin function shake128_squeeze
	.p2align	4
	.type	shake128_squeeze,@function
shake128_squeeze:                       # @shake128_squeeze
	.cfi_startproc
# %bb.0:
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%r12
	.cfi_def_cfa_offset 32
	pushq	%rbx
	.cfi_def_cfa_offset 40
	pushq	%rax
	.cfi_def_cfa_offset 48
	.cfi_offset %rbx, -40
	.cfi_offset %r12, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%rdx, %rbx
	movl	200(%rdx), %eax
	testq	%rsi, %rsi
	je	.LBB4_11
# %bb.1:
	movq	%rsi, %r14
	movq	%rdi, %r15
	movl	$168, %r12d
	jmp	.LBB4_4
	.p2align	4
.LBB4_2:                                #   in Loop: Header=BB4_4 Depth=1
	movl	%ecx, %eax
.LBB4_3:                                #   in Loop: Header=BB4_4 Depth=1
	movl	%eax, %edx
	subl	%ecx, %edx
	subq	%rdx, %r14
	je	.LBB4_11
.LBB4_4:                                # =>This Loop Header: Depth=1
                                        #     Child Loop BB4_8 Depth 2
	movl	%eax, %ecx
	cmpl	$168, %eax
	je	.LBB4_9
# %bb.5:                                #   in Loop: Header=BB4_4 Depth=1
	cmpl	$167, %ecx
	jbe	.LBB4_6
	jmp	.LBB4_2
	.p2align	4
.LBB4_9:                                #   in Loop: Header=BB4_4 Depth=1
	movq	%rbx, %rdi
	callq	KeccakF1600_StatePermute
	xorl	%ecx, %ecx
	cmpl	$167, %ecx
	ja	.LBB4_2
.LBB4_6:                                #   in Loop: Header=BB4_4 Depth=1
	movl	%ecx, %eax
	leaq	(%r14,%rax), %rdx
	cmpq	%rax, %rdx
	jbe	.LBB4_2
# %bb.7:                                #   in Loop: Header=BB4_4 Depth=1
	cmpq	$168, %rdx
	cmovaeq	%r12, %rdx
	leaq	(,%rax,8), %rsi
	.p2align	4
.LBB4_8:                                #   Parent Loop BB4_4 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	movq	%rax, %rdi
	andq	$-8, %rdi
	addq	%rbx, %rdi
	movl	%esi, %r8d
	andl	$56, %r8d
	shrl	$3, %r8d
	movzbl	(%r8,%rdi), %edi
	movb	%dil, (%r15)
	incq	%r15
	incq	%rax
	addq	$8, %rsi
	cmpq	%rdx, %rax
	jb	.LBB4_8
	jmp	.LBB4_3
.LBB4_11:
	movl	%eax, 200(%rbx)
	addq	$8, %rsp
	.cfi_def_cfa_offset 40
	popq	%rbx
	.cfi_def_cfa_offset 32
	popq	%r12
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end4:
	.size	shake128_squeeze, .Lfunc_end4-shake128_squeeze
	.cfi_endproc
                                        # -- End function
	.globl	shake128_absorb_once            # -- Begin function shake128_absorb_once
	.p2align	4
	.type	shake128_absorb_once,@function
shake128_absorb_once:                   # @shake128_absorb_once
	.cfi_startproc
# %bb.0:
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%rbx
	.cfi_def_cfa_offset 32
	.cfi_offset %rbx, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%rdi, %rbx
	vxorps	%xmm0, %xmm0, %xmm0
	vmovups	%ymm0, 160(%rdi)
	vmovups	%ymm0, 128(%rdi)
	vmovups	%ymm0, 96(%rdi)
	vmovups	%ymm0, 64(%rdi)
	vmovups	%ymm0, 32(%rdi)
	movq	%rdx, %r15
	movq	%rsi, %r14
	vmovups	%ymm0, (%rdi)
	movq	$0, 192(%rdi)
	cmpq	$168, %rdx
	jb	.LBB5_2
	.p2align	4
.LBB5_1:                                # =>This Inner Loop Header: Depth=1
	movq	(%r14), %rax
	xorq	%rax, (%rbx)
	movq	8(%r14), %rax
	xorq	%rax, 8(%rbx)
	movq	16(%r14), %rax
	xorq	%rax, 16(%rbx)
	movq	24(%r14), %rax
	xorq	%rax, 24(%rbx)
	movq	32(%r14), %rax
	xorq	%rax, 32(%rbx)
	movq	40(%r14), %rax
	xorq	%rax, 40(%rbx)
	movq	48(%r14), %rax
	xorq	%rax, 48(%rbx)
	movq	56(%r14), %rax
	xorq	%rax, 56(%rbx)
	movq	64(%r14), %rax
	xorq	%rax, 64(%rbx)
	movq	72(%r14), %rax
	xorq	%rax, 72(%rbx)
	movq	80(%r14), %rax
	xorq	%rax, 80(%rbx)
	movq	88(%r14), %rax
	xorq	%rax, 88(%rbx)
	movq	96(%r14), %rax
	xorq	%rax, 96(%rbx)
	movq	104(%r14), %rax
	xorq	%rax, 104(%rbx)
	movq	112(%r14), %rax
	xorq	%rax, 112(%rbx)
	movq	120(%r14), %rax
	xorq	%rax, 120(%rbx)
	movq	128(%r14), %rax
	xorq	%rax, 128(%rbx)
	movq	136(%r14), %rax
	xorq	%rax, 136(%rbx)
	movq	144(%r14), %rax
	xorq	%rax, 144(%rbx)
	movq	152(%r14), %rax
	xorq	%rax, 152(%rbx)
	movq	160(%r14), %rax
	xorq	%rax, 160(%rbx)
	addq	$168, %r14
	addq	$-168, %r15
	movq	%rbx, %rdi
	vzeroupper
	callq	KeccakF1600_StatePermute
	cmpq	$167, %r15
	ja	.LBB5_1
.LBB5_2:
	testq	%r15, %r15
	je	.LBB5_3
# %bb.4:
	movl	%r15d, %eax
	andl	$3, %eax
	cmpq	$4, %r15
	jae	.LBB5_6
# %bb.5:
	xorl	%ecx, %ecx
	xorl	%edx, %edx
	jmp	.LBB5_10
.LBB5_3:
	xorl	%edx, %edx
	jmp	.LBB5_12
.LBB5_6:
	andl	$252, %r15d
	movl	$24, %edx
	xorl	%ecx, %ecx
	.p2align	4
.LBB5_7:                                # =>This Inner Loop Header: Depth=1
	movzbl	(%r14,%rcx), %esi
	leal	-24(%rdx), %edi
	andb	$32, %dil
	shlxq	%rdi, %rsi, %rdi
	movl	%ecx, %esi
	andl	$-8, %esi
	xorq	(%rbx,%rsi), %rdi
	movq	%rdi, (%rbx,%rsi)
	movzbl	1(%r14,%rcx), %r8d
	leal	-16(%rdx), %r9d
	andb	$40, %r9b
	shlxq	%r9, %r8, %r8
	xorq	%rdi, %r8
	movq	%r8, (%rbx,%rsi)
	movzbl	2(%r14,%rcx), %edi
	leal	-8(%rdx), %r9d
	andb	$48, %r9b
	shlxq	%r9, %rdi, %rdi
	xorq	%r8, %rdi
	movq	%rdi, (%rbx,%rsi)
	movzbl	3(%r14,%rcx), %r8d
	movl	%edx, %r9d
	andb	$56, %r9b
	shlxq	%r9, %r8, %r8
	xorq	%rdi, %r8
	movq	%r8, (%rbx,%rsi)
	addq	$4, %rcx
	addl	$32, %edx
	cmpl	%ecx, %r15d
	jne	.LBB5_7
# %bb.8:
	testl	%eax, %eax
	je	.LBB5_13
# %bb.9:
	movl	%ecx, %edx
.LBB5_10:
	leal	(,%rdx,8), %esi
	.p2align	4
.LBB5_11:                               # =>This Inner Loop Header: Depth=1
	movzbl	(%r14,%rcx), %ecx
	movl	%esi, %edi
	andb	$56, %dil
	shlxq	%rdi, %rcx, %rcx
	movl	%edx, %edi
	andl	$-8, %edi
	xorq	%rcx, (%rbx,%rdi)
	incl	%edx
	addl	$8, %esi
	movq	%rdx, %rcx
	decl	%eax
	jne	.LBB5_11
.LBB5_12:
	leal	(,%rdx,8), %eax
	movl	$31, %ecx
	shlxq	%rax, %rcx, %rax
	andl	$-8, %edx
	xorq	%rax, (%rbx,%rdx)
	xorb	$-128, 167(%rbx)
	movl	$168, 200(%rbx)
	popq	%rbx
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	vzeroupper
	retq
.LBB5_13:
	.cfi_def_cfa_offset 32
	movl	%ecx, %edx
	jmp	.LBB5_12
.Lfunc_end5:
	.size	shake128_absorb_once, .Lfunc_end5-shake128_absorb_once
	.cfi_endproc
                                        # -- End function
	.globl	shake128_squeezeblocks          # -- Begin function shake128_squeezeblocks
	.p2align	4
	.type	shake128_squeezeblocks,@function
shake128_squeezeblocks:                 # @shake128_squeezeblocks
	.cfi_startproc
# %bb.0:
	testq	%rsi, %rsi
	je	.LBB6_4
# %bb.1:
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%rbx
	.cfi_def_cfa_offset 32
	.cfi_offset %rbx, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%rdx, %rbx
	movq	%rsi, %r14
	movq	%rdi, %r15
	.p2align	4
.LBB6_2:                                # =>This Inner Loop Header: Depth=1
	movq	%rbx, %rdi
	callq	KeccakF1600_StatePermute
	movq	(%rbx), %rax
	movq	%rax, (%r15)
	movq	8(%rbx), %rax
	movq	%rax, 8(%r15)
	movq	16(%rbx), %rax
	movq	%rax, 16(%r15)
	movq	24(%rbx), %rax
	movq	%rax, 24(%r15)
	movq	32(%rbx), %rax
	movq	%rax, 32(%r15)
	movq	40(%rbx), %rax
	movq	%rax, 40(%r15)
	movq	48(%rbx), %rax
	movq	%rax, 48(%r15)
	movq	56(%rbx), %rax
	movq	%rax, 56(%r15)
	movq	64(%rbx), %rax
	movq	%rax, 64(%r15)
	movq	72(%rbx), %rax
	movq	%rax, 72(%r15)
	movq	80(%rbx), %rax
	movq	%rax, 80(%r15)
	movq	88(%rbx), %rax
	movq	%rax, 88(%r15)
	movq	96(%rbx), %rax
	movq	%rax, 96(%r15)
	movq	104(%rbx), %rax
	movq	%rax, 104(%r15)
	movq	112(%rbx), %rax
	movq	%rax, 112(%r15)
	movq	120(%rbx), %rax
	movq	%rax, 120(%r15)
	movq	128(%rbx), %rax
	movq	%rax, 128(%r15)
	movq	136(%rbx), %rax
	movq	%rax, 136(%r15)
	movq	144(%rbx), %rax
	movq	%rax, 144(%r15)
	movq	152(%rbx), %rax
	movq	%rax, 152(%r15)
	movq	160(%rbx), %rax
	movq	%rax, 160(%r15)
	addq	$168, %r15
	decq	%r14
	jne	.LBB6_2
# %bb.3:
	popq	%rbx
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	.cfi_restore %rbx
	.cfi_restore %r14
	.cfi_restore %r15
.LBB6_4:
	retq
.Lfunc_end6:
	.size	shake128_squeezeblocks, .Lfunc_end6-shake128_squeezeblocks
	.cfi_endproc
                                        # -- End function
	.globl	shake256_init                   # -- Begin function shake256_init
	.p2align	4
	.type	shake256_init,@function
shake256_init:                          # @shake256_init
	.cfi_startproc
# %bb.0:
	vxorps	%xmm0, %xmm0, %xmm0
	vmovups	%ymm0, 172(%rdi)
	vmovups	%ymm0, 160(%rdi)
	vmovups	%ymm0, 128(%rdi)
	vmovups	%ymm0, 96(%rdi)
	vmovups	%ymm0, 64(%rdi)
	vmovups	%ymm0, 32(%rdi)
	vmovups	%ymm0, (%rdi)
	vzeroupper
	retq
.Lfunc_end7:
	.size	shake256_init, .Lfunc_end7-shake256_init
	.cfi_endproc
                                        # -- End function
	.globl	shake256_absorb                 # -- Begin function shake256_absorb
	.p2align	4
	.type	shake256_absorb,@function
shake256_absorb:                        # @shake256_absorb
	.cfi_startproc
# %bb.0:
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%rbx
	.cfi_def_cfa_offset 32
	.cfi_offset %rbx, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%rsi, %r14
	movq	%rdi, %rbx
	movl	200(%rdi), %eax
	movq	%rax, %rcx
	addq	%rdx, %rcx
	cmpq	$136, %rcx
	jae	.LBB8_6
# %bb.1:
	movq	%rcx, %r15
.LBB8_2:
	movl	%eax, %ecx
	cmpq	%rcx, %r15
	jbe	.LBB8_5
# %bb.3:
	leal	(,%rax,8), %ecx
	.p2align	4
.LBB8_4:                                # =>This Inner Loop Header: Depth=1
	movzbl	(%r14), %edx
	movl	%ecx, %esi
	andb	$56, %sil
	shlxq	%rsi, %rdx, %rdx
	movl	%eax, %esi
	andl	$-8, %esi
	xorq	%rdx, (%rbx,%rsi)
	incq	%r14
	incl	%eax
	addl	$8, %ecx
	cmpq	%rax, %r15
	ja	.LBB8_4
.LBB8_5:
	movl	%eax, 200(%rbx)
	popq	%rbx
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	retq
.LBB8_6:
	.cfi_def_cfa_offset 32
	movq	%rdx, %r15
	jmp	.LBB8_7
	.p2align	4
.LBB8_16:                               #   in Loop: Header=BB8_7 Depth=1
	movl	$136, %ecx
	subl	%eax, %ecx
	subq	%rcx, %r15
	movq	%rbx, %rdi
	callq	KeccakF1600_StatePermute
	xorl	%eax, %eax
	cmpq	$136, %r15
	jb	.LBB8_2
.LBB8_7:                                # =>This Loop Header: Depth=1
                                        #     Child Loop BB8_11 Depth 2
                                        #     Child Loop BB8_14 Depth 2
	cmpl	$135, %eax
	ja	.LBB8_16
# %bb.8:                                #   in Loop: Header=BB8_7 Depth=1
	movl	%eax, %edx
	negl	%edx
	andl	$3, %edx
	je	.LBB8_9
# %bb.10:                               #   in Loop: Header=BB8_7 Depth=1
	leal	(,%rax,8), %esi
	movl	%eax, %ecx
	.p2align	4
.LBB8_11:                               #   Parent Loop BB8_7 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	movzbl	(%r14), %edi
	movl	%esi, %r8d
	andb	$56, %r8b
	shlxq	%r8, %rdi, %rdi
	movl	%ecx, %r8d
	andl	$-8, %r8d
	xorq	%rdi, (%rbx,%r8)
	incq	%r14
	incl	%ecx
	addl	$8, %esi
	decl	%edx
	jne	.LBB8_11
# %bb.12:                               #   in Loop: Header=BB8_7 Depth=1
	cmpl	$132, %eax
	jbe	.LBB8_13
	jmp	.LBB8_16
	.p2align	4
.LBB8_9:                                #   in Loop: Header=BB8_7 Depth=1
	movl	%eax, %ecx
	cmpl	$132, %eax
	ja	.LBB8_16
.LBB8_13:                               #   in Loop: Header=BB8_7 Depth=1
	movl	%ecx, %edx
	shll	$3, %ecx
	xorl	%esi, %esi
	.p2align	4
.LBB8_14:                               #   Parent Loop BB8_7 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	leal	(%rdx,%rsi), %edi
	movzbl	(%r14,%rsi), %r8d
	movl	%ecx, %r9d
	andb	$56, %r9b
	shlxq	%r9, %r8, %r8
	andl	$-8, %edi
	xorq	%r8, (%rbx,%rdi)
	leal	(%rdx,%rsi), %edi
	incl	%edi
	movzbl	1(%r14,%rsi), %r8d
	leal	8(%rcx), %r9d
	andb	$56, %r9b
	shlxq	%r9, %r8, %r8
	andl	$-8, %edi
	xorq	%r8, (%rbx,%rdi)
	leal	(%rdx,%rsi), %edi
	addl	$2, %edi
	movzbl	2(%r14,%rsi), %r8d
	leal	16(%rcx), %r9d
	andb	$56, %r9b
	shlxq	%r9, %r8, %r8
	andl	$-8, %edi
	xorq	%r8, (%rbx,%rdi)
	leal	(%rdx,%rsi), %edi
	addl	$3, %edi
	movzbl	3(%r14,%rsi), %r8d
	leal	24(%rcx), %r9d
	andb	$56, %r9b
	shlxq	%r9, %r8, %r8
	andl	$-8, %edi
	xorq	%r8, (%rbx,%rdi)
	addq	$4, %rsi
	leal	(%rsi,%rdx), %edi
	addl	$32, %ecx
	cmpl	$136, %edi
	jne	.LBB8_14
# %bb.15:                               #   in Loop: Header=BB8_7 Depth=1
	addq	%rsi, %r14
	jmp	.LBB8_16
.Lfunc_end8:
	.size	shake256_absorb, .Lfunc_end8-shake256_absorb
	.cfi_endproc
                                        # -- End function
	.globl	shake256_finalize               # -- Begin function shake256_finalize
	.p2align	4
	.type	shake256_finalize,@function
shake256_finalize:                      # @shake256_finalize
	.cfi_startproc
# %bb.0:
	movl	200(%rdi), %eax
	leal	(,%rax,8), %ecx
	movl	$31, %edx
	shlxq	%rcx, %rdx, %rcx
	andl	$-8, %eax
	xorq	%rcx, (%rdi,%rax)
	xorb	$-128, 135(%rdi)
	movl	$136, 200(%rdi)
	retq
.Lfunc_end9:
	.size	shake256_finalize, .Lfunc_end9-shake256_finalize
	.cfi_endproc
                                        # -- End function
	.globl	shake256_squeeze                # -- Begin function shake256_squeeze
	.p2align	4
	.type	shake256_squeeze,@function
shake256_squeeze:                       # @shake256_squeeze
	.cfi_startproc
# %bb.0:
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%r12
	.cfi_def_cfa_offset 32
	pushq	%rbx
	.cfi_def_cfa_offset 40
	pushq	%rax
	.cfi_def_cfa_offset 48
	.cfi_offset %rbx, -40
	.cfi_offset %r12, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%rdx, %rbx
	movl	200(%rdx), %eax
	testq	%rsi, %rsi
	je	.LBB10_11
# %bb.1:
	movq	%rsi, %r14
	movq	%rdi, %r15
	movl	$136, %r12d
	jmp	.LBB10_4
	.p2align	4
.LBB10_2:                               #   in Loop: Header=BB10_4 Depth=1
	movl	%ecx, %eax
.LBB10_3:                               #   in Loop: Header=BB10_4 Depth=1
	movl	%eax, %edx
	subl	%ecx, %edx
	subq	%rdx, %r14
	je	.LBB10_11
.LBB10_4:                               # =>This Loop Header: Depth=1
                                        #     Child Loop BB10_8 Depth 2
	movl	%eax, %ecx
	cmpl	$136, %eax
	je	.LBB10_9
# %bb.5:                                #   in Loop: Header=BB10_4 Depth=1
	cmpl	$135, %ecx
	jbe	.LBB10_6
	jmp	.LBB10_2
	.p2align	4
.LBB10_9:                               #   in Loop: Header=BB10_4 Depth=1
	movq	%rbx, %rdi
	callq	KeccakF1600_StatePermute
	xorl	%ecx, %ecx
	cmpl	$135, %ecx
	ja	.LBB10_2
.LBB10_6:                               #   in Loop: Header=BB10_4 Depth=1
	movl	%ecx, %eax
	leaq	(%r14,%rax), %rdx
	cmpq	%rax, %rdx
	jbe	.LBB10_2
# %bb.7:                                #   in Loop: Header=BB10_4 Depth=1
	cmpq	$136, %rdx
	cmovaeq	%r12, %rdx
	leaq	(,%rax,8), %rsi
	.p2align	4
.LBB10_8:                               #   Parent Loop BB10_4 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	movq	%rax, %rdi
	andq	$-8, %rdi
	addq	%rbx, %rdi
	movl	%esi, %r8d
	andl	$56, %r8d
	shrl	$3, %r8d
	movzbl	(%r8,%rdi), %edi
	movb	%dil, (%r15)
	incq	%r15
	incq	%rax
	addq	$8, %rsi
	cmpq	%rdx, %rax
	jb	.LBB10_8
	jmp	.LBB10_3
.LBB10_11:
	movl	%eax, 200(%rbx)
	addq	$8, %rsp
	.cfi_def_cfa_offset 40
	popq	%rbx
	.cfi_def_cfa_offset 32
	popq	%r12
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end10:
	.size	shake256_squeeze, .Lfunc_end10-shake256_squeeze
	.cfi_endproc
                                        # -- End function
	.globl	shake256_absorb_once            # -- Begin function shake256_absorb_once
	.p2align	4
	.type	shake256_absorb_once,@function
shake256_absorb_once:                   # @shake256_absorb_once
	.cfi_startproc
# %bb.0:
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%rbx
	.cfi_def_cfa_offset 32
	.cfi_offset %rbx, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%rdi, %rbx
	vxorps	%xmm0, %xmm0, %xmm0
	vmovups	%ymm0, 160(%rdi)
	vmovups	%ymm0, 128(%rdi)
	vmovups	%ymm0, 96(%rdi)
	vmovups	%ymm0, 64(%rdi)
	vmovups	%ymm0, 32(%rdi)
	movq	%rdx, %r15
	movq	%rsi, %r14
	vmovups	%ymm0, (%rdi)
	movq	$0, 192(%rdi)
	cmpq	$136, %rdx
	jb	.LBB11_2
	.p2align	4
.LBB11_1:                               # =>This Inner Loop Header: Depth=1
	movq	(%r14), %rax
	xorq	%rax, (%rbx)
	movq	8(%r14), %rax
	xorq	%rax, 8(%rbx)
	movq	16(%r14), %rax
	xorq	%rax, 16(%rbx)
	movq	24(%r14), %rax
	xorq	%rax, 24(%rbx)
	movq	32(%r14), %rax
	xorq	%rax, 32(%rbx)
	movq	40(%r14), %rax
	xorq	%rax, 40(%rbx)
	movq	48(%r14), %rax
	xorq	%rax, 48(%rbx)
	movq	56(%r14), %rax
	xorq	%rax, 56(%rbx)
	movq	64(%r14), %rax
	xorq	%rax, 64(%rbx)
	movq	72(%r14), %rax
	xorq	%rax, 72(%rbx)
	movq	80(%r14), %rax
	xorq	%rax, 80(%rbx)
	movq	88(%r14), %rax
	xorq	%rax, 88(%rbx)
	movq	96(%r14), %rax
	xorq	%rax, 96(%rbx)
	movq	104(%r14), %rax
	xorq	%rax, 104(%rbx)
	movq	112(%r14), %rax
	xorq	%rax, 112(%rbx)
	movq	120(%r14), %rax
	xorq	%rax, 120(%rbx)
	movq	128(%r14), %rax
	xorq	%rax, 128(%rbx)
	addq	$136, %r14
	addq	$-136, %r15
	movq	%rbx, %rdi
	vzeroupper
	callq	KeccakF1600_StatePermute
	cmpq	$135, %r15
	ja	.LBB11_1
.LBB11_2:
	testq	%r15, %r15
	je	.LBB11_3
# %bb.4:
	movl	%r15d, %eax
	andl	$3, %eax
	cmpq	$4, %r15
	jae	.LBB11_6
# %bb.5:
	xorl	%ecx, %ecx
	xorl	%edx, %edx
	jmp	.LBB11_10
.LBB11_3:
	xorl	%edx, %edx
	jmp	.LBB11_12
.LBB11_6:
	andl	$252, %r15d
	movl	$24, %edx
	xorl	%ecx, %ecx
	.p2align	4
.LBB11_7:                               # =>This Inner Loop Header: Depth=1
	movzbl	(%r14,%rcx), %esi
	leal	-24(%rdx), %edi
	andb	$32, %dil
	shlxq	%rdi, %rsi, %rdi
	movl	%ecx, %esi
	andl	$-8, %esi
	xorq	(%rbx,%rsi), %rdi
	movq	%rdi, (%rbx,%rsi)
	movzbl	1(%r14,%rcx), %r8d
	leal	-16(%rdx), %r9d
	andb	$40, %r9b
	shlxq	%r9, %r8, %r8
	xorq	%rdi, %r8
	movq	%r8, (%rbx,%rsi)
	movzbl	2(%r14,%rcx), %edi
	leal	-8(%rdx), %r9d
	andb	$48, %r9b
	shlxq	%r9, %rdi, %rdi
	xorq	%r8, %rdi
	movq	%rdi, (%rbx,%rsi)
	movzbl	3(%r14,%rcx), %r8d
	movl	%edx, %r9d
	andb	$56, %r9b
	shlxq	%r9, %r8, %r8
	xorq	%rdi, %r8
	movq	%r8, (%rbx,%rsi)
	addq	$4, %rcx
	addl	$32, %edx
	cmpl	%ecx, %r15d
	jne	.LBB11_7
# %bb.8:
	testl	%eax, %eax
	je	.LBB11_13
# %bb.9:
	movl	%ecx, %edx
.LBB11_10:
	leal	(,%rdx,8), %esi
	.p2align	4
.LBB11_11:                              # =>This Inner Loop Header: Depth=1
	movzbl	(%r14,%rcx), %ecx
	movl	%esi, %edi
	andb	$56, %dil
	shlxq	%rdi, %rcx, %rcx
	movl	%edx, %edi
	andl	$-8, %edi
	xorq	%rcx, (%rbx,%rdi)
	incl	%edx
	addl	$8, %esi
	movq	%rdx, %rcx
	decl	%eax
	jne	.LBB11_11
.LBB11_12:
	leal	(,%rdx,8), %eax
	movl	$31, %ecx
	shlxq	%rax, %rcx, %rax
	andl	$-8, %edx
	xorq	%rax, (%rbx,%rdx)
	xorb	$-128, 135(%rbx)
	movl	$136, 200(%rbx)
	popq	%rbx
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	vzeroupper
	retq
.LBB11_13:
	.cfi_def_cfa_offset 32
	movl	%ecx, %edx
	jmp	.LBB11_12
.Lfunc_end11:
	.size	shake256_absorb_once, .Lfunc_end11-shake256_absorb_once
	.cfi_endproc
                                        # -- End function
	.globl	shake256_squeezeblocks          # -- Begin function shake256_squeezeblocks
	.p2align	4
	.type	shake256_squeezeblocks,@function
shake256_squeezeblocks:                 # @shake256_squeezeblocks
	.cfi_startproc
# %bb.0:
	testq	%rsi, %rsi
	je	.LBB12_4
# %bb.1:
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%rbx
	.cfi_def_cfa_offset 32
	.cfi_offset %rbx, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%rdx, %rbx
	movq	%rsi, %r14
	movq	%rdi, %r15
	.p2align	4
.LBB12_2:                               # =>This Inner Loop Header: Depth=1
	movq	%rbx, %rdi
	callq	KeccakF1600_StatePermute
	movq	(%rbx), %rax
	movq	%rax, (%r15)
	movq	8(%rbx), %rax
	movq	%rax, 8(%r15)
	movq	16(%rbx), %rax
	movq	%rax, 16(%r15)
	movq	24(%rbx), %rax
	movq	%rax, 24(%r15)
	movq	32(%rbx), %rax
	movq	%rax, 32(%r15)
	movq	40(%rbx), %rax
	movq	%rax, 40(%r15)
	movq	48(%rbx), %rax
	movq	%rax, 48(%r15)
	movq	56(%rbx), %rax
	movq	%rax, 56(%r15)
	movq	64(%rbx), %rax
	movq	%rax, 64(%r15)
	movq	72(%rbx), %rax
	movq	%rax, 72(%r15)
	movq	80(%rbx), %rax
	movq	%rax, 80(%r15)
	movq	88(%rbx), %rax
	movq	%rax, 88(%r15)
	movq	96(%rbx), %rax
	movq	%rax, 96(%r15)
	movq	104(%rbx), %rax
	movq	%rax, 104(%r15)
	movq	112(%rbx), %rax
	movq	%rax, 112(%r15)
	movq	120(%rbx), %rax
	movq	%rax, 120(%r15)
	movq	128(%rbx), %rax
	movq	%rax, 128(%r15)
	addq	$136, %r15
	decq	%r14
	jne	.LBB12_2
# %bb.3:
	popq	%rbx
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	.cfi_restore %rbx
	.cfi_restore %r14
	.cfi_restore %r15
.LBB12_4:
	retq
.Lfunc_end12:
	.size	shake256_squeezeblocks, .Lfunc_end12-shake256_squeezeblocks
	.cfi_endproc
                                        # -- End function
	.globl	shake128                        # -- Begin function shake128
	.p2align	4
	.type	shake128,@function
shake128:                               # @shake128
	.cfi_startproc
# %bb.0:
	pushq	%rbp
	.cfi_def_cfa_offset 16
	pushq	%r15
	.cfi_def_cfa_offset 24
	pushq	%r14
	.cfi_def_cfa_offset 32
	pushq	%r13
	.cfi_def_cfa_offset 40
	pushq	%r12
	.cfi_def_cfa_offset 48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	subq	$216, %rsp
	.cfi_def_cfa_offset 272
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rsi, %r14
	movq	%rdi, %rbx
	leaq	8(%rsp), %rdi
	movq	%rdx, %rsi
	movq	%rcx, %rdx
	callq	shake128_absorb_once
	movq	%r14, %rdx
	shrq	$3, %rdx
	movabsq	$878416384462359601, %rax       # imm = 0xC30C30C30C30C31
	mulxq	%rax, %r13, %r13
	imulq	$168, %r13, %r12
	movq	%r14, %r15
	subq	%r12, %r15
	cmpq	$168, %r14
	jb	.LBB13_3
# %bb.1:
	leaq	8(%rsp), %r14
	movq	%rbx, %rbp
	.p2align	4
.LBB13_2:                               # =>This Inner Loop Header: Depth=1
	movq	%r14, %rdi
	vzeroupper
	callq	KeccakF1600_StatePermute
	vmovups	8(%rsp), %ymm0
	vmovups	%ymm0, (%rbp)
	vmovups	40(%rsp), %ymm0
	vmovups	%ymm0, 32(%rbp)
	vmovups	72(%rsp), %ymm0
	vmovups	%ymm0, 64(%rbp)
	vmovups	104(%rsp), %ymm0
	vmovups	%ymm0, 96(%rbp)
	vmovups	136(%rsp), %ymm0
	vmovups	%ymm0, 128(%rbp)
	movq	168(%rsp), %rax
	movq	%rax, 160(%rbp)
	addq	$168, %rbp
	decq	%r13
	jne	.LBB13_2
.LBB13_3:
	testq	%r15, %r15
	je	.LBB13_14
# %bb.4:
	movl	208(%rsp), %eax
	addq	%r12, %rbx
	leaq	8(%rsp), %r14
	movl	$168, %r12d
	jmp	.LBB13_7
	.p2align	4
.LBB13_5:                               #   in Loop: Header=BB13_7 Depth=1
	movl	%ecx, %eax
.LBB13_6:                               #   in Loop: Header=BB13_7 Depth=1
	movl	%eax, %edx
	subl	%ecx, %edx
	subq	%rdx, %r15
	je	.LBB13_14
.LBB13_7:                               # =>This Loop Header: Depth=1
                                        #     Child Loop BB13_11 Depth 2
	movl	%eax, %ecx
	cmpl	$168, %eax
	je	.LBB13_12
# %bb.8:                                #   in Loop: Header=BB13_7 Depth=1
	cmpl	$167, %ecx
	jbe	.LBB13_9
	jmp	.LBB13_5
	.p2align	4
.LBB13_12:                              #   in Loop: Header=BB13_7 Depth=1
	movq	%r14, %rdi
	vzeroupper
	callq	KeccakF1600_StatePermute
	xorl	%ecx, %ecx
	cmpl	$167, %ecx
	ja	.LBB13_5
.LBB13_9:                               #   in Loop: Header=BB13_7 Depth=1
	movl	%ecx, %eax
	leaq	(%r15,%rax), %rdx
	cmpq	%rax, %rdx
	jbe	.LBB13_5
# %bb.10:                               #   in Loop: Header=BB13_7 Depth=1
	cmpq	$168, %rdx
	cmovaeq	%r12, %rdx
	leaq	(,%rax,8), %rsi
	.p2align	4
.LBB13_11:                              #   Parent Loop BB13_7 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	movq	%rax, %rdi
	andq	$-8, %rdi
	addq	%rsp, %rdi
	addq	$8, %rdi
	movl	%esi, %r8d
	andl	$56, %r8d
	shrl	$3, %r8d
	movzbl	(%r8,%rdi), %edi
	movb	%dil, (%rbx)
	incq	%rbx
	incq	%rax
	addq	$8, %rsi
	cmpq	%rdx, %rax
	jb	.LBB13_11
	jmp	.LBB13_6
.LBB13_14:
	addq	$216, %rsp
	.cfi_def_cfa_offset 56
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%r12
	.cfi_def_cfa_offset 40
	popq	%r13
	.cfi_def_cfa_offset 32
	popq	%r14
	.cfi_def_cfa_offset 24
	popq	%r15
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	vzeroupper
	retq
.Lfunc_end13:
	.size	shake128, .Lfunc_end13-shake128
	.cfi_endproc
                                        # -- End function
	.globl	shake256                        # -- Begin function shake256
	.p2align	4
	.type	shake256,@function
shake256:                               # @shake256
	.cfi_startproc
# %bb.0:
	pushq	%rbp
	.cfi_def_cfa_offset 16
	pushq	%r15
	.cfi_def_cfa_offset 24
	pushq	%r14
	.cfi_def_cfa_offset 32
	pushq	%r13
	.cfi_def_cfa_offset 40
	pushq	%r12
	.cfi_def_cfa_offset 48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	subq	$216, %rsp
	.cfi_def_cfa_offset 272
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rsi, %r14
	movq	%rdi, %rbx
	leaq	8(%rsp), %rdi
	movq	%rdx, %rsi
	movq	%rcx, %rdx
	callq	shake256_absorb_once
	movabsq	$-1085102592571150095, %rax     # imm = 0xF0F0F0F0F0F0F0F1
	movq	%r14, %rdx
	mulxq	%rax, %rax, %rax
	movq	%rax, %r12
	shrq	$7, %r12
	andq	$-128, %rax
	leaq	(%rax,%r12,8), %rax
	movq	%r14, %r15
	subq	%rax, %r15
	cmpq	$136, %r14
	jb	.LBB14_3
# %bb.1:
	leaq	8(%rsp), %r14
	movq	%rbx, %r13
	movq	%r12, %rbp
	.p2align	4
.LBB14_2:                               # =>This Inner Loop Header: Depth=1
	movq	%r14, %rdi
	vzeroupper
	callq	KeccakF1600_StatePermute
	vmovups	8(%rsp), %ymm0
	vmovups	%ymm0, (%r13)
	vmovups	40(%rsp), %ymm0
	vmovups	%ymm0, 32(%r13)
	vmovups	72(%rsp), %ymm0
	vmovups	%ymm0, 64(%r13)
	vmovups	104(%rsp), %ymm0
	vmovups	%ymm0, 96(%r13)
	movq	136(%rsp), %rax
	movq	%rax, 128(%r13)
	addq	$136, %r13
	decq	%rbp
	jne	.LBB14_2
.LBB14_3:
	testq	%r15, %r15
	je	.LBB14_14
# %bb.4:
	movq	%r12, %rax
	shlq	$7, %rax
	leaq	(%rax,%r12,8), %rcx
	movl	208(%rsp), %eax
	addq	%rcx, %rbx
	leaq	8(%rsp), %r14
	movl	$136, %r12d
	jmp	.LBB14_7
	.p2align	4
.LBB14_5:                               #   in Loop: Header=BB14_7 Depth=1
	movl	%ecx, %eax
.LBB14_6:                               #   in Loop: Header=BB14_7 Depth=1
	movl	%eax, %edx
	subl	%ecx, %edx
	subq	%rdx, %r15
	je	.LBB14_14
.LBB14_7:                               # =>This Loop Header: Depth=1
                                        #     Child Loop BB14_11 Depth 2
	movl	%eax, %ecx
	cmpl	$136, %eax
	je	.LBB14_12
# %bb.8:                                #   in Loop: Header=BB14_7 Depth=1
	cmpl	$135, %ecx
	jbe	.LBB14_9
	jmp	.LBB14_5
	.p2align	4
.LBB14_12:                              #   in Loop: Header=BB14_7 Depth=1
	movq	%r14, %rdi
	vzeroupper
	callq	KeccakF1600_StatePermute
	xorl	%ecx, %ecx
	cmpl	$135, %ecx
	ja	.LBB14_5
.LBB14_9:                               #   in Loop: Header=BB14_7 Depth=1
	movl	%ecx, %eax
	leaq	(%r15,%rax), %rdx
	cmpq	%rax, %rdx
	jbe	.LBB14_5
# %bb.10:                               #   in Loop: Header=BB14_7 Depth=1
	cmpq	$136, %rdx
	cmovaeq	%r12, %rdx
	leaq	(,%rax,8), %rsi
	.p2align	4
.LBB14_11:                              #   Parent Loop BB14_7 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	movq	%rax, %rdi
	andq	$-8, %rdi
	addq	%rsp, %rdi
	addq	$8, %rdi
	movl	%esi, %r8d
	andl	$56, %r8d
	shrl	$3, %r8d
	movzbl	(%r8,%rdi), %edi
	movb	%dil, (%rbx)
	incq	%rbx
	incq	%rax
	addq	$8, %rsi
	cmpq	%rdx, %rax
	jb	.LBB14_11
	jmp	.LBB14_6
.LBB14_14:
	addq	$216, %rsp
	.cfi_def_cfa_offset 56
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%r12
	.cfi_def_cfa_offset 40
	popq	%r13
	.cfi_def_cfa_offset 32
	popq	%r14
	.cfi_def_cfa_offset 24
	popq	%r15
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	vzeroupper
	retq
.Lfunc_end14:
	.size	shake256, .Lfunc_end14-shake256
	.cfi_endproc
                                        # -- End function
	.globl	sha3_256                        # -- Begin function sha3_256
	.p2align	4
	.type	sha3_256,@function
sha3_256:                               # @sha3_256
	.cfi_startproc
# %bb.0:
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%r12
	.cfi_def_cfa_offset 32
	pushq	%rbx
	.cfi_def_cfa_offset 40
	subq	$200, %rsp
	.cfi_def_cfa_offset 240
	.cfi_offset %rbx, -40
	.cfi_offset %r12, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	vxorps	%xmm0, %xmm0, %xmm0
	vmovups	%ymm0, 160(%rsp)
	vmovups	%ymm0, 128(%rsp)
	vmovups	%ymm0, 96(%rsp)
	vmovups	%ymm0, 64(%rsp)
	vmovups	%ymm0, 32(%rsp)
	movq	%rdx, %r15
	movq	%rsi, %r14
	movq	%rdi, %rbx
	vmovups	%ymm0, (%rsp)
	movq	$0, 192(%rsp)
	cmpq	$136, %rdx
	jb	.LBB15_3
# %bb.1:
	movq	%rsp, %r12
	.p2align	4
.LBB15_2:                               # =>This Inner Loop Header: Depth=1
	vmovups	(%rsp), %ymm0
	vmovups	32(%rsp), %ymm1
	vmovups	64(%rsp), %ymm2
	vmovups	96(%rsp), %ymm3
	vxorps	(%r14), %ymm0, %ymm0
	vmovups	%ymm0, (%rsp)
	vxorps	32(%r14), %ymm1, %ymm0
	vmovups	%ymm0, 32(%rsp)
	vxorps	64(%r14), %ymm2, %ymm0
	vmovups	%ymm0, 64(%rsp)
	vxorps	96(%r14), %ymm3, %ymm0
	vmovups	%ymm0, 96(%rsp)
	movq	128(%r14), %rax
	xorq	%rax, 128(%rsp)
	addq	$136, %r14
	addq	$-136, %r15
	movq	%r12, %rdi
	vzeroupper
	callq	KeccakF1600_StatePermute
	cmpq	$135, %r15
	ja	.LBB15_2
.LBB15_3:
	testq	%r15, %r15
	je	.LBB15_4
# %bb.5:
	movl	%r15d, %eax
	andl	$3, %eax
	cmpq	$4, %r15
	jae	.LBB15_7
# %bb.6:
	xorl	%ecx, %ecx
	xorl	%edx, %edx
	jmp	.LBB15_11
.LBB15_4:
	xorl	%edx, %edx
	jmp	.LBB15_13
.LBB15_7:
	andl	$252, %r15d
	movl	$24, %edx
	xorl	%ecx, %ecx
	.p2align	4
.LBB15_8:                               # =>This Inner Loop Header: Depth=1
	movzbl	(%r14,%rcx), %esi
	leal	-24(%rdx), %edi
	andb	$32, %dil
	shlxq	%rdi, %rsi, %rdi
	movl	%ecx, %esi
	andl	$-8, %esi
	xorq	(%rsp,%rsi), %rdi
	movq	%rdi, (%rsp,%rsi)
	movzbl	1(%r14,%rcx), %r8d
	leal	-16(%rdx), %r9d
	andb	$40, %r9b
	shlxq	%r9, %r8, %r8
	xorq	%rdi, %r8
	movq	%r8, (%rsp,%rsi)
	movzbl	2(%r14,%rcx), %edi
	leal	-8(%rdx), %r9d
	andb	$48, %r9b
	shlxq	%r9, %rdi, %rdi
	xorq	%r8, %rdi
	movq	%rdi, (%rsp,%rsi)
	movzbl	3(%r14,%rcx), %r8d
	movl	%edx, %r9d
	andb	$56, %r9b
	shlxq	%r9, %r8, %r8
	xorq	%rdi, %r8
	movq	%r8, (%rsp,%rsi)
	addq	$4, %rcx
	addl	$32, %edx
	cmpl	%ecx, %r15d
	jne	.LBB15_8
# %bb.9:
	testl	%eax, %eax
	je	.LBB15_14
# %bb.10:
	movl	%ecx, %edx
.LBB15_11:
	leal	(,%rdx,8), %esi
	.p2align	4
.LBB15_12:                              # =>This Inner Loop Header: Depth=1
	movzbl	(%r14,%rcx), %ecx
	movl	%esi, %edi
	andb	$56, %dil
	shlxq	%rdi, %rcx, %rcx
	movl	%edx, %edi
	andl	$-8, %edi
	xorq	%rcx, (%rsp,%rdi)
	incl	%edx
	addl	$8, %esi
	movq	%rdx, %rcx
	decl	%eax
	jne	.LBB15_12
.LBB15_13:
	leal	(,%rdx,8), %eax
	movl	$6, %ecx
	shlxq	%rax, %rcx, %rax
	andl	$-8, %edx
	xorq	%rax, (%rsp,%rdx)
	xorb	$-128, 135(%rsp)
	movq	%rsp, %rdi
	vzeroupper
	callq	KeccakF1600_StatePermute
	vmovups	(%rsp), %ymm0
	vmovups	%ymm0, (%rbx)
	addq	$200, %rsp
	.cfi_def_cfa_offset 40
	popq	%rbx
	.cfi_def_cfa_offset 32
	popq	%r12
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	vzeroupper
	retq
.LBB15_14:
	.cfi_def_cfa_offset 240
	movl	%ecx, %edx
	jmp	.LBB15_13
.Lfunc_end15:
	.size	sha3_256, .Lfunc_end15-sha3_256
	.cfi_endproc
                                        # -- End function
	.globl	sha3_512                        # -- Begin function sha3_512
	.p2align	4
	.type	sha3_512,@function
sha3_512:                               # @sha3_512
	.cfi_startproc
# %bb.0:
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%r12
	.cfi_def_cfa_offset 32
	pushq	%rbx
	.cfi_def_cfa_offset 40
	subq	$200, %rsp
	.cfi_def_cfa_offset 240
	.cfi_offset %rbx, -40
	.cfi_offset %r12, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	vxorps	%xmm0, %xmm0, %xmm0
	vmovups	%ymm0, 160(%rsp)
	vmovups	%ymm0, 128(%rsp)
	vmovups	%ymm0, 96(%rsp)
	vmovups	%ymm0, 64(%rsp)
	vmovups	%ymm0, 32(%rsp)
	movq	%rdx, %r15
	movq	%rsi, %r14
	movq	%rdi, %rbx
	vmovups	%ymm0, (%rsp)
	movq	$0, 192(%rsp)
	cmpq	$72, %rdx
	jb	.LBB16_3
# %bb.1:
	movq	%rsp, %r12
	.p2align	4
.LBB16_2:                               # =>This Inner Loop Header: Depth=1
	vmovups	(%rsp), %ymm0
	vmovups	32(%rsp), %ymm1
	vxorps	(%r14), %ymm0, %ymm0
	vmovups	%ymm0, (%rsp)
	vxorps	32(%r14), %ymm1, %ymm0
	vmovups	%ymm0, 32(%rsp)
	movq	64(%r14), %rax
	xorq	%rax, 64(%rsp)
	addq	$72, %r14
	addq	$-72, %r15
	movq	%r12, %rdi
	vzeroupper
	callq	KeccakF1600_StatePermute
	cmpq	$71, %r15
	ja	.LBB16_2
.LBB16_3:
	testq	%r15, %r15
	je	.LBB16_4
# %bb.5:
	movl	%r15d, %eax
	andl	$3, %eax
	cmpq	$4, %r15
	jae	.LBB16_7
# %bb.6:
	xorl	%ecx, %ecx
	xorl	%edx, %edx
	jmp	.LBB16_11
.LBB16_4:
	xorl	%edx, %edx
	jmp	.LBB16_13
.LBB16_7:
	andl	$124, %r15d
	movl	$24, %edx
	xorl	%ecx, %ecx
	.p2align	4
.LBB16_8:                               # =>This Inner Loop Header: Depth=1
	movzbl	(%r14,%rcx), %esi
	leal	-24(%rdx), %edi
	andb	$32, %dil
	shlxq	%rdi, %rsi, %rdi
	movl	%ecx, %esi
	andl	$-8, %esi
	xorq	(%rsp,%rsi), %rdi
	movq	%rdi, (%rsp,%rsi)
	movzbl	1(%r14,%rcx), %r8d
	leal	-16(%rdx), %r9d
	andb	$40, %r9b
	shlxq	%r9, %r8, %r8
	xorq	%rdi, %r8
	movq	%r8, (%rsp,%rsi)
	movzbl	2(%r14,%rcx), %edi
	leal	-8(%rdx), %r9d
	andb	$48, %r9b
	shlxq	%r9, %rdi, %rdi
	xorq	%r8, %rdi
	movq	%rdi, (%rsp,%rsi)
	movzbl	3(%r14,%rcx), %r8d
	movl	%edx, %r9d
	andb	$56, %r9b
	shlxq	%r9, %r8, %r8
	xorq	%rdi, %r8
	movq	%r8, (%rsp,%rsi)
	addq	$4, %rcx
	addl	$32, %edx
	cmpl	%ecx, %r15d
	jne	.LBB16_8
# %bb.9:
	testl	%eax, %eax
	je	.LBB16_14
# %bb.10:
	movl	%ecx, %edx
.LBB16_11:
	leal	(,%rdx,8), %esi
	.p2align	4
.LBB16_12:                              # =>This Inner Loop Header: Depth=1
	movzbl	(%r14,%rcx), %ecx
	movl	%esi, %edi
	andb	$56, %dil
	shlxq	%rdi, %rcx, %rcx
	movl	%edx, %edi
	andl	$-8, %edi
	xorq	%rcx, (%rsp,%rdi)
	incl	%edx
	addl	$8, %esi
	movq	%rdx, %rcx
	decl	%eax
	jne	.LBB16_12
.LBB16_13:
	leal	(,%rdx,8), %eax
	movl	$6, %ecx
	shlxq	%rax, %rcx, %rax
	andl	$-8, %edx
	xorq	%rax, (%rsp,%rdx)
	xorb	$-128, 71(%rsp)
	movq	%rsp, %rdi
	vzeroupper
	callq	KeccakF1600_StatePermute
	vmovups	(%rsp), %ymm0
	vmovups	32(%rsp), %ymm1
	vmovups	%ymm1, 32(%rbx)
	vmovups	%ymm0, (%rbx)
	addq	$200, %rsp
	.cfi_def_cfa_offset 40
	popq	%rbx
	.cfi_def_cfa_offset 32
	popq	%r12
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	vzeroupper
	retq
.LBB16_14:
	.cfi_def_cfa_offset 240
	movl	%ecx, %edx
	jmp	.LBB16_13
.Lfunc_end16:
	.size	sha3_512, .Lfunc_end16-sha3_512
	.cfi_endproc
                                        # -- End function
	.globl	scloudplus_F                    # -- Begin function scloudplus_F
	.p2align	4
	.type	scloudplus_F,@function
scloudplus_F:                           # @scloudplus_F
	.cfi_startproc
# %bb.0:
	jmp	shake256                        # TAILCALL
.Lfunc_end17:
	.size	scloudplus_F, .Lfunc_end17-scloudplus_F
	.cfi_endproc
                                        # -- End function
	.globl	scloudplus_K                    # -- Begin function scloudplus_K
	.p2align	4
	.type	scloudplus_K,@function
scloudplus_K:                           # @scloudplus_K
	.cfi_startproc
# %bb.0:
	jmp	shake256                        # TAILCALL
.Lfunc_end18:
	.size	scloudplus_K, .Lfunc_end18-scloudplus_K
	.cfi_endproc
                                        # -- End function
	.globl	scloudplus_H                    # -- Begin function scloudplus_H
	.p2align	4
	.type	scloudplus_H,@function
scloudplus_H:                           # @scloudplus_H
	.cfi_startproc
# %bb.0:
	jmp	sha3_256                        # TAILCALL
.Lfunc_end19:
	.size	scloudplus_H, .Lfunc_end19-scloudplus_H
	.cfi_endproc
                                        # -- End function
	.globl	scloudplus_G                    # -- Begin function scloudplus_G
	.p2align	4
	.type	scloudplus_G,@function
scloudplus_G:                           # @scloudplus_G
	.cfi_startproc
# %bb.0:
	jmp	sha3_512                        # TAILCALL
.Lfunc_end20:
	.size	scloudplus_G, .Lfunc_end20-scloudplus_G
	.cfi_endproc
                                        # -- End function
	.type	KeccakF_RoundConstants,@object  # @KeccakF_RoundConstants
	.section	.rodata,"a",@progbits
	.p2align	4, 0x0
KeccakF_RoundConstants:
	.quad	1                               # 0x1
	.quad	32898                           # 0x8082
	.quad	-9223372036854742902            # 0x800000000000808a
	.quad	-9223372034707259392            # 0x8000000080008000
	.quad	32907                           # 0x808b
	.quad	2147483649                      # 0x80000001
	.quad	-9223372034707259263            # 0x8000000080008081
	.quad	-9223372036854743031            # 0x8000000000008009
	.quad	138                             # 0x8a
	.quad	136                             # 0x88
	.quad	2147516425                      # 0x80008009
	.quad	2147483658                      # 0x8000000a
	.quad	2147516555                      # 0x8000808b
	.quad	-9223372036854775669            # 0x800000000000008b
	.quad	-9223372036854742903            # 0x8000000000008089
	.quad	-9223372036854743037            # 0x8000000000008003
	.quad	-9223372036854743038            # 0x8000000000008002
	.quad	-9223372036854775680            # 0x8000000000000080
	.quad	32778                           # 0x800a
	.quad	-9223372034707292150            # 0x800000008000000a
	.quad	-9223372034707259263            # 0x8000000080008081
	.quad	-9223372036854742912            # 0x8000000000008080
	.quad	2147483649                      # 0x80000001
	.quad	-9223372034707259384            # 0x8000000080008008
	.size	KeccakF_RoundConstants, 192

	.ident	"Debian clang version 22.1.6 (++20260514074242+fc4aad7b5db3-1~exp1~20260514074407.73)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
