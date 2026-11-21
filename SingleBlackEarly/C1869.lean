import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1869 : checkSingleBlackFast (-62, -39) 14471 .west (18, 28) (-47, 8) = true := by
  decide +kernel

end LangtonsAnt
