import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1601 : checkSingleBlackFast (-39, -11) 27843 .east (9, -1) (-20, -19) = true := by
  decide +kernel

end LangtonsAnt
