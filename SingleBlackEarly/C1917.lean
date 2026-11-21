import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1917 : checkSingleBlackFast (-67, -43) 14783 .west (20, 31) (-50, 12) = true := by
  decide +kernel

end LangtonsAnt
