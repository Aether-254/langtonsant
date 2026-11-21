import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1618 : checkSingleBlackFast2 (-39, -13) 11372 .north (8, 0) (-34, -16) = true := by
  decide +kernel

end LangtonsAnt
