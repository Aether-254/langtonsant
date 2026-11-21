import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1669 : checkSingleBlackFast2 (-44, -19) 17083 .east (10, 13) (-12, -30) = true := by
  decide +kernel

end LangtonsAnt
