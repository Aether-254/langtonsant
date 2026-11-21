import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1851 : checkSingleBlackFast (-61, -37) 14471 .west (17, 28) (-47, 9) = true := by
  decide +kernel

end LangtonsAnt
