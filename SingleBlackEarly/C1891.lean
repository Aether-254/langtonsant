import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1891 : checkSingleBlackFast (-64, -41) 14575 .west (19, 29) (-48, 9) = true := by
  decide +kernel

end LangtonsAnt
