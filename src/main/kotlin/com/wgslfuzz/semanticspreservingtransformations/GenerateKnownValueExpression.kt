package com.wgslfuzz.semanticspreservingtransformations

import com.wgslfuzz.core.AugmentedExpression
import com.wgslfuzz.core.BinaryOperator
import com.wgslfuzz.core.Expression
import com.wgslfuzz.core.ShaderJob
import com.wgslfuzz.core.Type
import com.wgslfuzz.core.UnaryOperator
import com.wgslfuzz.core.clone
import kotlin.math.max
import kotlin.math.truncate

private const val OVERFLOW_MODULO_OF_32_BIT_WIDTH = 4294967296

fun generateKnownValueInteger(
    depth: Int,
    knownValue: Int,
    type: Type.Integer,
    fuzzerSettings: FuzzerSettings,
    shaderJob: ShaderJob,
): AugmentedExpression.KnownValue =
    if (knownValue >= 0) {
        generateKnownValueIntegerHelper(depth, knownValue.toLong(), type, fuzzerSettings, shaderJob)
    } else {
        val knownValueExpression = generateKnownValueIntegerHelper(depth, -(knownValue.toLong()), type, fuzzerSettings, shaderJob)

        AugmentedExpression.KnownValue(
            knownValue = constantWithSameValueEverywhere(knownValue, type),
            expression =
                Expression.Unary(
                    operator = UnaryOperator.MINUS,
                    target = knownValueExpression.expression,
                ),
        )
    }

private fun generateKnownValueIntegerHelper(
    depth: Int,
    knownValue: Long,
    type: Type.Integer,
    fuzzerSettings: FuzzerSettings,
    shaderJob: ShaderJob,
): AugmentedExpression.KnownValue {
    require(0 <= knownValue && knownValue < OVERFLOW_MODULO_OF_32_BIT_WIDTH) { "Internal generateKnownValueInteger error" }
    if (fuzzerSettings.goDeeper(depth)) {
        return AugmentedExpression.KnownValue(
            knownValue = constantWithSameValueEverywhere(knownValue.toInt(), type),
            expression = constantWithSameValueEverywhere(knownValue.toInt(), type),
        )
    }

    val choices: List<Pair<Int, () -> AugmentedExpression.KnownValue>> =
        listOfNotNull(
            fuzzerSettings.knownValueWeights.plainKnownValue(depth) to {
                AugmentedExpression.KnownValue(
                    knownValue = constantWithSameValueEverywhere(knownValue.toInt(), type),
                    expression = constantWithSameValueEverywhere(knownValue.toInt(), type),
                )
            },
            fuzzerSettings.knownValueWeights.sumOfKnownValues(depth) to {
                // TODO(Get a better distribution for random numbers as otherwise will only ever have overflows)
                val randomValue = fuzzerSettings.randomInt(Int.MAX_VALUE).toLong()
                val difference: Long =
                    if (knownValue - randomValue >= 0) {
                        knownValue - randomValue
                    } else {
                        knownValue - randomValue + OVERFLOW_MODULO_OF_32_BIT_WIDTH
                    }
                AugmentedExpression.KnownValue(
                    knownValue = constantWithSameValueEverywhere(knownValue.toInt(), type),
                    expression =
                        binaryExpressionRandomOperandOrder(
                            fuzzerSettings,
                            BinaryOperator.PLUS,
                            generateKnownValueIntegerHelper(
                                depth = depth + 1,
                                knownValue = randomValue,
                                type = type,
                                fuzzerSettings = fuzzerSettings,
                                shaderJob = shaderJob,
                            ),
                            generateKnownValueIntegerHelper(
                                depth = depth + 1,
                                knownValue = difference,
                                type = type,
                                fuzzerSettings = fuzzerSettings,
                                shaderJob = shaderJob,
                            ),
                        ),
                )
            },
            fuzzerSettings.knownValueWeights.differenceOfKnownValues(depth) to {
                val randomValue = fuzzerSettings.randomInt(Int.MAX_VALUE).toLong()
                val sum: Long =
                    if (knownValue + randomValue < OVERFLOW_MODULO_OF_32_BIT_WIDTH) {
                        knownValue + randomValue
                    } else {
                        knownValue + randomValue - OVERFLOW_MODULO_OF_32_BIT_WIDTH
                    }
                AugmentedExpression.KnownValue(
                    knownValue = constantWithSameValueEverywhere(knownValue.toInt(), type),
                    expression =
                        binaryExpressionRandomOperandOrder(
                            fuzzerSettings,
                            BinaryOperator.MINUS,
                            generateKnownValueIntegerHelper(
                                depth = depth + 1,
                                knownValue = randomValue,
                                type = type,
                                fuzzerSettings = fuzzerSettings,
                                shaderJob = shaderJob,
                            ),
                            generateKnownValueIntegerHelper(
                                depth = depth + 1,
                                knownValue = sum,
                                type = type,
                                fuzzerSettings = fuzzerSettings,
                                shaderJob = shaderJob,
                            ),
                        ),
                )
            },
            fuzzerSettings.knownValueWeights.productOfKnownValues(depth) to {
                if (fuzzerSettings.randomInt(100) < 50) {
                    // This path will likely use overflow of the multiplication
                    val randomValue = fuzzerSettings.randomInt(Int.MAX_VALUE).toLong()
                    var i = 0
                    while ((knownValue + i * OVERFLOW_MODULO_OF_32_BIT_WIDTH) % randomValue != 0.toLong()) {
                        i++
                    }
                    val quotient = (knownValue + i * OVERFLOW_MODULO_OF_32_BIT_WIDTH) % randomValue
                    AugmentedExpression.KnownValue(
                        knownValue = constantWithSameValueEverywhere(knownValue.toInt(), type),
                        expression =
                            binaryExpressionRandomOperandOrder(
                                fuzzerSettings,
                                BinaryOperator.TIMES,
                                generateKnownValueIntegerHelper(
                                    depth = depth + 1,
                                    knownValue = randomValue,
                                    type = type,
                                    fuzzerSettings = fuzzerSettings,
                                    shaderJob = shaderJob,
                                ),
                                generateKnownValueIntegerHelper(
                                    depth = depth + 1,
                                    knownValue = quotient,
                                    type = type,
                                    fuzzerSettings = fuzzerSettings,
                                    shaderJob = shaderJob,
                                ),
                            ),
                    )
                } else {
                    // Finds a factor
                    val randomValue: Long = max(1, fuzzerSettings.randomInt(max(1, knownValue.toInt() / 2))).toLong()
                    val quotient: Long = knownValue / randomValue
                    val remainder: Long = knownValue % randomValue

                    var resultExpression =
                        binaryExpressionRandomOperandOrder(
                            fuzzerSettings,
                            BinaryOperator.TIMES,
                            generateKnownValueIntegerHelper(
                                depth = depth + 1,
                                knownValue = randomValue,
                                type = type,
                                fuzzerSettings = fuzzerSettings,
                                shaderJob = shaderJob,
                            ),
                            generateKnownValueIntegerHelper(
                                depth = depth + 1,
                                knownValue = quotient,
                                type = type,
                                fuzzerSettings = fuzzerSettings,
                                shaderJob = shaderJob,
                            ),
                        )
                    if (remainder != 0.toLong() || fuzzerSettings.randomBool()) {
                        resultExpression =
                            binaryExpressionRandomOperandOrder(
                                fuzzerSettings,
                                BinaryOperator.PLUS,
                                resultExpression,
                                generateKnownValueIntegerHelper(
                                    depth = depth + 1,
                                    knownValue = remainder,
                                    type = type,
                                    fuzzerSettings = fuzzerSettings,
                                    shaderJob = shaderJob,
                                ),
                            )
                    }
                    AugmentedExpression.KnownValue(
                        knownValue = constantWithSameValueEverywhere(knownValue.toInt(), type),
                        expression = resultExpression,
                    )
                }
            },
            if (type.isAbstract()) {
                null
            } else {
                // Deriving a known value from a uniform only works with concrete types.
                fuzzerSettings.knownValueWeights.knownValueDerivedFromUniform(depth) to {
                    val (uniformScalarExpression, valueOfUniformExpression, scalarType) =
                        randomUniformScalarWithValue(
                            shaderJob,
                            fuzzerSettings,
                        )

                    val valueOfUniformAsDouble = getValueAsDoubleFromConstant(valueOfUniformExpression)
                    val (valueOfAdjustedUniform, uniformScalarAdjustedExpression) =
                        if (scalarType is Type.Float || scalarType != type) {
                            when (type) {
                                Type.AbstractInteger -> throw AssertionError("Type should not be Abstract")
                                Type.I32 ->
                                    Pair(
                                        valueOfUniformAsDouble.toLong(),
                                        Expression.I32ValueConstructor(
                                            listOf(uniformScalarExpression),
                                        ),
                                    )
                                Type.U32 ->
                                    Pair(
                                        valueOfUniformAsDouble.toLong(),
                                        Expression.U32ValueConstructor(
                                            listOf(uniformScalarExpression),
                                        ),
                                    )
                            }
                        } else if (truncate(valueOfUniformAsDouble) == valueOfUniformAsDouble) {
                            Pair(valueOfUniformAsDouble.toLong(), uniformScalarExpression)
                        } else {
                            Pair(truncate(valueOfUniformAsDouble).toLong(), truncateExpression(uniformScalarExpression))
                        }

                    val expression =
                        if (valueOfAdjustedUniform == knownValue) {
                            uniformScalarAdjustedExpression
                        } else if (valueOfAdjustedUniform > knownValue) {
                            val difference = valueOfAdjustedUniform - knownValue
                            Expression.Binary(
                                BinaryOperator.MINUS,
                                uniformScalarAdjustedExpression,
                                generateKnownValueIntegerHelper(
                                    depth = depth + 1,
                                    knownValue = difference,
                                    fuzzerSettings = fuzzerSettings,
                                    shaderJob = shaderJob,
                                    type = type,
                                ),
                            )
                        } else {
                            val difference = knownValue - valueOfAdjustedUniform
                            binaryExpressionRandomOperandOrder(
                                fuzzerSettings,
                                BinaryOperator.PLUS,
                                uniformScalarAdjustedExpression,
                                generateKnownValueIntegerHelper(
                                    depth = depth + 1,
                                    knownValue = difference,
                                    fuzzerSettings = fuzzerSettings,
                                    shaderJob = shaderJob,
                                    type = type,
                                ),
                            )
                        }

                    AugmentedExpression.KnownValue(
                        knownValue = constantWithSameValueEverywhere(knownValue.toInt(), type),
                        expression = expression,
                    )
                }
            },
        )
    return choose(fuzzerSettings, choices)
}

fun generateKnownValueExpression(
    depth: Int,
    knownValue: Expression,
    type: Type,
    fuzzerSettings: FuzzerSettings,
    shaderJob: ShaderJob,
): AugmentedExpression.KnownValue {
    if (!fuzzerSettings.goDeeper(depth)) {
        return AugmentedExpression.KnownValue(
            knownValue = knownValue.clone(),
            expression = knownValue.clone(),
        )
    }
    if (type !is Type.Scalar) {
        TODO("Need to support non-scalar known values, e.g. vectors and matrices.")
    }
    val knownValueAsInt: Int =
        getNumericValueFromConstant(
            knownValue,
        )
    if (type is Type.Integer) {
        return generateKnownValueInteger(depth, knownValueAsInt, type, fuzzerSettings, shaderJob)
    }
    if (knownValueAsInt !in 0..LARGEST_INTEGER_IN_PRECISE_FLOAT_RANGE) {
        throw UnsupportedOperationException("Known values are currently only supported within a limited range.")
    }
    val literalSuffix =
        when (type) {
            is Type.F32 -> "f"
            is Type.AbstractFloat -> ""
            else -> throw RuntimeException("Unsupported type.")
        }

    val choices: List<Pair<Int, () -> AugmentedExpression.KnownValue>> =
        listOfNotNull(
            fuzzerSettings.knownValueWeights.plainKnownValue(depth) to {
                AugmentedExpression.KnownValue(
                    knownValue = knownValue.clone(),
                    expression = knownValue.clone(),
                )
            },
            fuzzerSettings.knownValueWeights.sumOfKnownValues(depth) to {
                val randomValue = fuzzerSettings.randomInt(knownValueAsInt + 1)
                assert(randomValue <= knownValueAsInt)
                val difference: Int = knownValueAsInt - randomValue
                assert(difference in 0..knownValueAsInt)
                val randomValueText = "$randomValue$literalSuffix"
                val differenceText = "$difference$literalSuffix"
                val randomValueKnownExpression =

                    Expression.FloatLiteral(randomValueText)

                val differenceKnownExpression =
                    if (type is Type.Integer) {
                        Expression.IntLiteral(differenceText)
                    } else {
                        Expression.FloatLiteral(differenceText)
                    }
                AugmentedExpression.KnownValue(
                    knownValue = knownValue.clone(),
                    expression =
                        binaryExpressionRandomOperandOrder(
                            fuzzerSettings,
                            BinaryOperator.PLUS,
                            generateKnownValueExpression(
                                depth = depth + 1,
                                knownValue = randomValueKnownExpression,
                                type = type,
                                fuzzerSettings = fuzzerSettings,
                                shaderJob = shaderJob,
                            ),
                            generateKnownValueExpression(
                                depth = depth + 1,
                                knownValue = differenceKnownExpression,
                                type = type,
                                fuzzerSettings = fuzzerSettings,
                                shaderJob = shaderJob,
                            ),
                        ),
                )
            },
            fuzzerSettings.knownValueWeights.differenceOfKnownValues(depth) to {
                val randomValue = fuzzerSettings.randomInt(LARGEST_INTEGER_IN_PRECISE_FLOAT_RANGE - knownValueAsInt + 1)
                val sum: Int = knownValueAsInt + randomValue
                assert(sum in 0..LARGEST_INTEGER_IN_PRECISE_FLOAT_RANGE)
                val randomValueText = "$randomValue$literalSuffix"
                val sumText = "$sum$literalSuffix"
                val randomValueKnownExpression = Expression.FloatLiteral(randomValueText)

                val sumKnownExpression = Expression.IntLiteral(sumText)
                AugmentedExpression.KnownValue(
                    knownValue = knownValue.clone(),
                    expression =
                        Expression.Binary(
                            BinaryOperator.MINUS,
                            generateKnownValueExpression(
                                depth = depth + 1,
                                knownValue = sumKnownExpression,
                                type = type,
                                fuzzerSettings = fuzzerSettings,
                                shaderJob = shaderJob,
                            ),
                            generateKnownValueExpression(
                                depth = depth + 1,
                                knownValue = randomValueKnownExpression,
                                type = type,
                                fuzzerSettings = fuzzerSettings,
                                shaderJob = shaderJob,
                            ),
                        ),
                )
            },
            fuzzerSettings.knownValueWeights.productOfKnownValues(depth) to {
                val randomValue = max(1, fuzzerSettings.randomInt(max(1, knownValueAsInt / 2)))
                val quotient: Int = knownValueAsInt / randomValue
                val remainder: Int = knownValueAsInt % randomValue

                val randomValueText = "$randomValue$literalSuffix"
                val quotientText = "$quotient$literalSuffix"
                val remainderText = "$remainder$literalSuffix"
                val randomValueKnownExpression = Expression.FloatLiteral(randomValueText)

                val quotientKnownExpression = Expression.FloatLiteral(quotientText)
                val remainderKnownExpression = Expression.FloatLiteral(remainderText)

                var resultExpression =
                    binaryExpressionRandomOperandOrder(
                        fuzzerSettings,
                        BinaryOperator.TIMES,
                        generateKnownValueExpression(
                            depth = depth + 1,
                            knownValue = randomValueKnownExpression,
                            type = type,
                            fuzzerSettings = fuzzerSettings,
                            shaderJob = shaderJob,
                        ),
                        generateKnownValueExpression(
                            depth = depth + 1,
                            knownValue = quotientKnownExpression,
                            type = type,
                            fuzzerSettings = fuzzerSettings,
                            shaderJob = shaderJob,
                        ),
                    )
                if (remainder != 0 || fuzzerSettings.randomBool()) {
                    resultExpression =
                        binaryExpressionRandomOperandOrder(
                            fuzzerSettings,
                            BinaryOperator.PLUS,
                            resultExpression,
                            generateKnownValueExpression(
                                depth = depth + 1,
                                knownValue = remainderKnownExpression,
                                type = type,
                                fuzzerSettings = fuzzerSettings,
                                shaderJob = shaderJob,
                            ),
                        )
                }
                AugmentedExpression.KnownValue(
                    knownValue = knownValue.clone(),
                    expression = resultExpression,
                )
            },
            if (type.isAbstract()) {
                null
            } else {
                // Deriving a known value from a uniform only works with concrete types.
                fuzzerSettings.knownValueWeights.knownValueDerivedFromUniform(depth) to {
                    val (uniformScalar, valueOfUniform, scalarType) = randomUniformScalarWithValue(shaderJob, fuzzerSettings)
                    val (valueOfUniformAdjusted, uniformScalarAdjusted) =
                        getNumericValueWithAdjustedExpression(
                            valueExpression = uniformScalar,
                            valueExpressionType = scalarType,
                            constantExpression = valueOfUniform,
                            outputType = type,
                        )
                    val expression =
                        if (valueOfUniformAdjusted == knownValueAsInt) {
                            uniformScalarAdjusted
                        } else if (valueOfUniformAdjusted > knownValueAsInt) {
                            val difference = valueOfUniformAdjusted - knownValueAsInt
                            val differenceText = "$difference$literalSuffix"
                            val differenceKnownExpression =
                                if (type is Type.Integer) {
                                    Expression.IntLiteral(differenceText)
                                } else {
                                    Expression.FloatLiteral(differenceText)
                                }
                            Expression.Binary(
                                BinaryOperator.MINUS,
                                uniformScalarAdjusted,
                                generateKnownValueExpression(
                                    depth = depth + 1,
                                    knownValue = differenceKnownExpression,
                                    fuzzerSettings = fuzzerSettings,
                                    shaderJob = shaderJob,
                                    type = type,
                                ),
                            )
                        } else {
                            val difference = knownValueAsInt - valueOfUniformAdjusted
                            val differenceText = "$difference$literalSuffix"
                            val differenceKnownExpression =
                                if (type is Type.Integer) {
                                    Expression.IntLiteral(differenceText)
                                } else {
                                    Expression.FloatLiteral(differenceText)
                                }
                            binaryExpressionRandomOperandOrder(
                                fuzzerSettings,
                                BinaryOperator.PLUS,
                                uniformScalarAdjusted,
                                generateKnownValueExpression(
                                    depth = depth + 1,
                                    knownValue = differenceKnownExpression,
                                    fuzzerSettings = fuzzerSettings,
                                    shaderJob = shaderJob,
                                    type = type,
                                ),
                            )
                        }
                    AugmentedExpression.KnownValue(
                        knownValue = knownValue.clone(),
                        expression = expression,
                    )
                }
            },
        )
    return choose(fuzzerSettings, choices)
}

private fun getNumericValueFromConstant(constantExpression: Expression): Int {
    val result = getValueAsDoubleFromConstant(constantExpression)
    if (result.toInt().toDouble() != result) {
        throw RuntimeException("Only integer-valued doubles are supported in known value expressions.")
    }
    return result.toInt()
}

/**
 * Takes in a constant expression and determines its value and outputs the expression if changes were made to make it conform to requirements.
 * Requirements:
 * - Correct output type
 * - If the value is a float with a fractional it truncates it
 */
private fun getNumericValueWithAdjustedExpression(
    valueExpression: Expression,
    valueExpressionType: Type,
    constantExpression: Expression,
    outputType: Type,
): Pair<Int, Expression> {
    val value = getValueAsDoubleFromConstant(constantExpression)

    val truncate = value.toInt().toDouble() != value

    val outputExpressionWithCastIfNeeded =
        if (outputType is Type.U32) {
            // This truncates - https://www.w3.org/TR/WGSL/#u32-builtin
            Expression.U32ValueConstructor(listOf(valueExpression))
        } else if (valueExpressionType is Type.Integer && outputType is Type.Float) {
            // Should not have to truncate a scalar of type Integer
            assert(!truncate)
            Expression.F32ValueConstructor(listOf(valueExpression))
        } else if (valueExpressionType is Type.Float && outputType is Type.Integer) {
            // This truncates https://www.w3.org/TR/WGSL/#i32-builtin
            Expression.I32ValueConstructor(listOf(valueExpression))
        } else if (truncate) {
            truncateExpression(valueExpression)
        } else {
            valueExpression
        }

    val truncatedValue = truncate(value)

    val (outputValueInRangeAndInteger, outputExpressionWithCastAndInRange) =
        if (truncatedValue !in
            0.0..LARGEST_INTEGER_IN_PRECISE_FLOAT_RANGE.toDouble()
        ) {
            val largestIntegerInPreciseFloatRangeExpression =
                when (outputType) {
                    is Type.U32, is Type.I32 -> Expression.IntLiteral(LARGEST_INTEGER_IN_PRECISE_FLOAT_RANGE.toString())
                    is Type.F32 -> Expression.FloatLiteral(LARGEST_INTEGER_IN_PRECISE_FLOAT_RANGE.toString())
                    else -> throw UnsupportedOperationException("Cannot create a expression of this type")
                }
            Pair(
                truncatedValue.mod(LARGEST_INTEGER_IN_PRECISE_FLOAT_RANGE.toDouble()),
                modExpression(absExpression(outputExpressionWithCastIfNeeded), largestIntegerInPreciseFloatRangeExpression),
            )
        } else {
            Pair(truncatedValue, outputExpressionWithCastIfNeeded)
        }

    return Pair(outputValueInRangeAndInteger.toInt(), outputExpressionWithCastAndInRange)
}

private fun getValueAsDoubleFromConstant(constantExpression: Expression): Double =
    when (constantExpression) {
        is Expression.FloatLiteral -> constantExpression.text.trimEnd('f', 'h').toDouble()
        is Expression.IntLiteral -> constantExpression.text.trimEnd('i', 'u').toDouble()
        else -> throw UnsupportedOperationException("Cannot get numeric value from $constantExpression")
    }

private fun truncateExpression(expression: Expression) =
    Expression.FunctionCall(
        callee = "trunc",
        templateParameter = null,
        args = listOf(expression),
    )

private fun modExpression(
    expression: Expression,
    modByExpression: Expression,
) = Expression.Binary(
    operator = BinaryOperator.MODULO,
    lhs = expression,
    rhs = modByExpression,
)

private fun absExpression(expression: Expression) =
    Expression.FunctionCall(
        callee = "abs",
        templateParameter = null,
        args = listOf(expression),
    )
