import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1872 : checkSingleBlackFast (-63, -40) 19749 .east (29, 14) (6, -48) = true := by
  decide +kernel

end LangtonsAnt
