import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1583 : checkSingleBlackFast (-36, -13) 13119 .west (5, 15) (-34, -5) = true := by
  decide +kernel

end LangtonsAnt
