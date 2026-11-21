import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1956 : checkSingleBlackFast2 (-69, -47) 16313 .west (22, 31) (-51, 11) = true := by
  decide +kernel

end LangtonsAnt
