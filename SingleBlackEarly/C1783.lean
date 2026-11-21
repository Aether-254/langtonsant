import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1783 : checkSingleBlackFast2 (-54, -32) 18611 .east (17, 11) (-16, -29) = true := by
  decide +kernel

end LangtonsAnt
